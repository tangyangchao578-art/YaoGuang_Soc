`ifndef NOC_ROUTING_SEQ_SV
`define NOC_ROUTING_SEQ_SV

class noc_routing_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_routing_seq)

    rand int       num_transactions;

    constraint trans_cons {
        num_transactions inside {[100:500]};
    }

    function new(string name = "noc_routing_seq");
        super.new(name);
        num_transactions = 200;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            noc_seq_item req;
            req = noc_seq_item::type_id::create("req");
            start_item(req);
            randomize(req) with {
                packet_type inside {NOC_PACKET_READ, NOC_PACKET_WRITE};
                src_id != dst_id;
                qos_level == 0;
            };
            finish_item(req);
        end
    endtask
endclass

class noc_mesh_routing_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_mesh_routing_seq)

    int       num_packets_per_pair;

    function new(string name = "noc_mesh_routing_seq");
        super.new(name);
        num_packets_per_pair = 20;
    endtask

    task body();
        for(int src = 0; src < 8; src++) begin
            for(int dst = 0; dst < 8; dst++) begin
                if(src == dst) continue;
                for(int i = 0; i < num_packets_per_pair; i++) begin
                    noc_seq_item req;
                    req = noc_seq_item::type_id::create("req");
                    start_item(req);
                    req.packet_type = $random() % 2 ? NOC_PACKET_READ : NOC_PACKET_WRITE;
                    req.src_id      = src;
                    req.dst_id      = dst;
                    req.addr        = (dst << 20) | (i * 64);
                    req.qos_level   = 0;
                    req.burst_size  = $urandom_range(0, 3);
                    req.length      = $urandom_range(1, 16);
                    finish_item(req);
                end
            end
        end
    endtask
endclass

class noc_all_to_all_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_all_to_all_seq)

    int       packets_per_node;

    function new(string name = "noc_all_to_all_seq");
        super.new(name);
        packets_per_node = 50;
    endtask

    task body();
        for(int src = 0; src < 8; src++) begin
            for(int i = 0; i < packets_per_node; i++) begin
                noc_seq_item req;
                req = noc_seq_item::type_id::create("req");
                start_item(req);
                req.packet_type = $random() % 2 ? NOC_PACKET_READ : NOC_PACKET_WRITE;
                req.src_id      = src;
                req.dst_id      = $urandom_range(0, 7);
                req.addr        = (req.dst_id << 20) | (i * 64);
                req.qos_level   = $urandom_range(0, 3);
                req.burst_size  = $urandom_range(0, 3);
                req.length      = $urandom_range(1, 64);
                finish_item(req);
            end
        end
    endtask
endclass

`endif
