//-----------------------------------------------------------------------------
// File: l3_cache_reference_model.sv
// Description: L3 Cache reference model
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_REFERENCE_MODEL_SV
`define L3_CACHE_REFERENCE_MODEL_SV

class l3_cache_reference_model extends uvm_component;
    `uvm_component_utils(l3_cache_reference_model)

    uvm_tlm_analysis_fifo#(l3_cache_transaction) input_fifo;
    uvm_tlm_analysis_fifo#(l3_cache_transaction) output_fifo;

    bit [63:0] l3_tag [`MAX_BANKS][`MAX_WAYS][`MAX_INDEX];
    bit [511:0] l3_data [`MAX_BANKS][`MAX_WAYS][`MAX_INDEX];
    bit l3_valid [`MAX_BANKS][`MAX_WAYS][`MAX_INDEX];
    bit l3_dirty [`MAX_BANKS][`MAX_WAYS][`MAX_INDEX];
    bit [3:0] l3_lru [`MAX_BANKS][`MAX_INDEX];

    int bank_select(bit [63:0] addr);
        return addr[11:8];
    endfunction

    int index_select(bit [63:0] addr);
        return addr[7:2];
    endfunction

    function new(string name, uvm_component parent);
        super.new(name, parent);
        input_fifo = new("input_fifo", this);
        output_fifo = new("output_fifo", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        initialize_l3_cache();
    endfunction

    function void initialize_l3_cache();
        for(int b = 0; b < `MAX_BANKS; b++) begin
            for(int w = 0; w < `MAX_WAYS; w++) begin
                for(int i = 0; i < `MAX_INDEX; i++) begin
                    l3_tag[b][w][i] = 0;
                    l3_data[b][w][i] = 0;
                    l3_valid[b][w][i] = 0;
                    l3_dirty[b][w][i] = 0;
                end
            end
            for(int i = 0; i < `MAX_INDEX; i++) begin
                l3_lru[b][i] = 0;
            end
        end
    endfunction

    task run_phase(uvm_phase phase);
        l3_cache_transaction tr;
        super.run_phase(phase);
        fork
            process_transactions();
        join_none
    endtask

    task process_transactions();
        forever begin
            input_fifo.get(tr);
            process_l3_access(tr);
        end
    endtask

    function void process_l3_access(l3_cache_transaction tr);
        int bank, idx, way;
        l3_cache_transaction resp_tr;

        bank = bank_select(tr.addr);
        idx = index_select(tr.addr);

        resp_tr = new();
        resp_tr.addr = tr.addr;
        resp_tr.id = tr.id;
        resp_tr.op = tr.op;

        case(tr.op)
            L3_OP_READ: begin
                if(search_cache(tr.addr, bank, idx, way)) begin
                    resp_tr.data = l3_data[bank][way][idx];
                    resp_tr.response = L3_RESP_HIT;
                    update_lru(bank, idx, way);
                end else begin
                    resp_tr.data = $urandom();
                    resp_tr.response = L3_RESP_MISS;
                    allocate_line(bank, idx, way, tr.addr, resp_tr.data);
                end
            end
            L3_OP_WRITE: begin
                if(search_cache(tr.addr, bank, idx, way)) begin
                    l3_data[bank][way][idx] = tr.data;
                    l3_dirty[bank][way][idx] = 1;
                    resp_tr.response = L3_RESP_HIT;
                    update_lru(bank, idx, way);
                end else begin
                    resp_tr.response = L3_RESP_MISS;
                    if(`ENABLE_ALLOCATE) begin
                        allocate_line(bank, idx, way, tr.addr, tr.data);
                    end
                end
            end
            L3_OP_CLEAN: begin
                if(search_cache(tr.addr, bank, idx, way)) begin
                    l3_dirty[bank][way][idx] = 0;
                    resp_tr.response = L3_RESP_HIT;
                end else begin
                    resp_tr.response = L3_RESP_MISS;
                end
            end
            L3_OP_INVALIDATE: begin
                if(search_cache(tr.addr, bank, idx, way)) begin
                    l3_valid[bank][way][idx] = 0;
                    resp_tr.response = L3_RESP_HIT;
                end else begin
                    resp_tr.response = L3_RESP_MISS;
                end
            end
            default: begin
                resp_tr.response = L3_RESP_HIT;
            end
        endcase

        output_fifo.write(resp_tr);
    endfunction

    function bit search_cache(bit [63:0] addr, int bank, int idx, output int way);
        bit [63:0] tag;
        tag = addr[63:12];
        for(int w = 0; w < `MAX_WAYS; w++) begin
            if(l3_valid[bank][w][idx] && l3_tag[bank][w][idx] == tag) begin
                way = w;
                return 1;
            end
        end
        return 0;
    endfunction

    function void allocate_line(int bank, int idx, int way, bit [63:0] addr, bit [511:0] data);
        bit [63:0] tag;
        int victim;

        tag = addr[63:12];
        victim = get_lru_way(bank, idx);

        if(l3_dirty[bank][victim][idx]) begin
            evict_line(bank, victim, idx);
        end

        l3_tag[bank][victim][idx] = tag;
        l3_data[bank][victim][idx] = data;
        l3_valid[bank][victim][idx] = 1;
        l3_dirty[bank][victim][idx] = 0;
    endfunction

    function int get_lru_way(int bank, int idx);
        return l3_lru[bank][idx];
    endfunction

    function void update_lru(int bank, int idx, int way);
        l3_lru[bank][idx] = way;
    endfunction

    function void evict_line(int bank, int way, int idx);
        l3_valid[bank][way][idx] = 0;
    endfunction
endclass

`define MAX_BANKS 16
`define MAX_WAYS 16
`define MAX_INDEX 1024
`define ENABLE_ALLOCATE 1
`endif
