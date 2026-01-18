`ifndef NOC_QOS_SEQ_SV
`define NOC_QOS_SEQ_SV

class noc_qos_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_qos_seq)

    rand int       num_transactions;

    constraint trans_cons {
        num_transactions inside {[200:1000]};
    }

    function new(string name = "noc_qos_seq");
        super.new(name);
        num_transactions = 500;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            noc_seq_item req;
            req = noc_seq_item::type_id::create("req");
            start_item(req);
            randomize(req) with {
                packet_type inside {NOC_PACKET_READ, NOC_PACKET_WRITE};
                qos_level dist {0:/25, 1:/25, 2:/25, 3:/25};
            };
            finish_item(req);
        end
    endtask
endclass

class noc_qos_priority_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_qos_priority_seq)

    int       high_priority_packets;
    int       low_priority_packets;

    function new(string name = "noc_qos_priority_seq");
        super.new(name);
        high_priority_packets = 100;
        low_priority_packets = 500;
    endtask

    task body();
        fork
            begin
                for(int i = 0; i < low_priority_packets; i++) begin
                    noc_seq_item req;
                    req = noc_seq_item::type_id::create("req");
                    start_item(req);
                    req.packet_type = NOC_PACKET_READ;
                    req.src_id      = $urandom_range(0, 7);
                    req.dst_id      = $urandom_range(0, 7);
                    req.qos_level   = 0;
                    req.length      = $urandom_range(1, 32);
                    finish_item(req);
                end
            end
            begin
                for(int i = 0; i < high_priority_packets; i++) begin
                    noc_seq_item req;
                    req = noc_seq_item::type_id::create("req");
                    start_item(req);
                    req.packet_type = NOC_PACKET_WRITE;
                    req.src_id      = $urandom_range(0, 7);
                    req.dst_id      = $urandom_range(0, 7);
                    req.qos_level   = 3;
                    req.length      = $urandom_range(1, 8);
                    finish_item(req);
                end
            end
        join
    endtask
endclass

class noc_qos_fairness_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_qos_fairness_seq)

    int       packets_per_qos;

    function new(string name = "noc_qos_fairness_seq");
        super.new(name);
        packets_per_qos = 200;
    endtask

    task body();
        for(int qos = 0; qos < 4; qos++) begin
            for(int i = 0; i < packets_per_qos; i++) begin
                noc_seq_item req;
                req = noc_seq_item::type_id::create("req");
                start_item(req);
                req.packet_type = $random() % 2 ? NOC_PACKET_READ : NOC_PACKET_WRITE;
                req.src_id      = $urandom_range(0, 7);
                req.dst_id      = $urandom_range(0, 7);
                req.qos_level   = qos;
                req.length      = $urandom_range(1, 16);
                finish_item(req);
            end
        end
    endtask
endclass

`endif
