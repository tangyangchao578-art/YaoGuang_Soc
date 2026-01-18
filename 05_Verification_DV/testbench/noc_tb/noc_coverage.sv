`ifndef NOC_COVERAGE_SV
`define NOC_COVERAGE_SV

class noc_coverage extends uvm_subscriber#(noc_seq_item);
    `uvm_component_utils(noc_coverage)

    noc_seq_item  trans;

    covergroup noc_cg;
        option.per_instance = 1;
        packet_type: coverpoint trans.packet_type {
            bins READ     = {NOC_PACKET_READ};
            bins WRITE    = {NOC_PACKET_WRITE};
            bins ATOMIC   = {NOC_PACKET_ATOMIC};
            bins CONTROL  = {NOC_PACKET_CONTROL};
        }
        src_id: coverpoint trans.src_id {
            bins SRC_0  = {0};
            bins SRC_1  = {1};
            bins SRC_2  = {2};
            bins SRC_3  = {3};
            bins SRC_4  = {4};
            bins SRC_5  = {5};
            bins SRC_6  = {6};
            bins SRC_7  = {7};
        }
        dst_id: coverpoint trans.dst_id {
            bins DST_0  = {0};
            bins DST_1  = {1};
            bins DST_2  = {2};
            bins DST_3  = {3};
            bins DST_4  = {4};
            bins DST_5  = {5};
            bins DST_6  = {6};
            bins DST_7  = {7};
        }
        qos_level: coverpoint trans.qos_level {
            bins QOS_0 = {0};
            bins QOS_1 = {1};
            bins QOS_2 = {2};
            bins QOS_3 = {3};
        }
        burst_size: coverpoint trans.burst_size {
            bins BS_1  = {0};
            bins BS_4  = {1};
            bins BS_8  = {2};
            bins BS_16 = {3};
        }
        status: coverpoint trans.status {
            bins SUCCESS = {0};
            bins ERR_TIMEOUT = {NOC_ERR_TIMEOUT};
            bins ERR_DEADLOCK = {NOC_ERR_DEADLOCK};
            bins ERR_CRC = {NOC_ERR_CRC};
        }
        cross_src_dst: cross src_id, dst_id;
        cross_qos: cross packet_type, qos_level;
    endgroup

    function new(string name = "noc_coverage", uvm_component parent = null);
        super.new(name, parent);
        noc_cg = new();
    endfunction

    virtual function void write(T t);
        trans = t;
        noc_cg.sample();
    endfunction

    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_name(), $sformatf("NoC Coverage Report:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Overall Coverage: %0.2f%%", noc_cg.get_inst_coverage()), UVM_LOW)
    endfunction
endclass

`endif
