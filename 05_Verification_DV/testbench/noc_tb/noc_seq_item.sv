`ifndef NOC_SEQ_ITEM_SV
`define NOC_SEQ_ITEM_SV

typedef enum bit[7:0] {
    NOC_PACKET_READ   = 8'h01,
    NOC_PACKET_WRITE  = 8'h02,
    NOC_PACKET_ATOMIC = 8'h03,
    NOC_PACKET_CONTROL = 8'h04
} noc_packet_type_e;

typedef enum bit[7:0] {
    NOC_ERR_NONE     = 8'h00,
    NOC_ERR_TIMEOUT  = 8'hE1,
    NOC_ERR_DEADLOCK = 8'hE2,
    NOC_ERR_CRC      = 8'hE3,
    NOC_ERR_ROUTE    = 8'hE4
} noc_status_e;

class noc_seq_item extends uvm_sequence_item;
    `uvm_object_utils(noc_seq_item)

    rand noc_packet_type_e  packet_type;
    rand bit[3:0]           src_id;
    rand bit[3:0]           dst_id;
    rand bit[31:0]          addr;
    rand bit[7:0]           qos_level;
    rand bit[1:0]           burst_size;
    rand bit[7:0]           length;
    bit[31:0]               packet_id;
    bit[127:0]              data;
    bit                     status;
    string                  op_name;

    constraint valid_ids {
        src_id inside {[0:7]};
        dst_id inside {[0:7]};
    }

    constraint valid_qos {
        qos_level inside {[0:3]};
    }

    constraint valid_burst {
        burst_size inside {0, 1, 2, 3};
    }

    constraint valid_length {
        length inside {[1:64]};
    }

    function new(string name = "noc_seq_item");
        super.new(name);
        packet_id = $random();
        op_name = packet_type.name();
    endfunction

    function string convert2string();
        return $sformatf("type=%s src=%0d dst=%0d addr=0x%08x qos=%0d len=%0d status=%0d",
            op_name, src_id, dst_id, addr, qos_level, length, status);
    endfunction
endclass

`endif
