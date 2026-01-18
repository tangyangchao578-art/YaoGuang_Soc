`ifndef PMU_SEQ_ITEM_SV
`define PMU_SEQ_ITEM_SV

typedef enum bit[7:0] {
    PMU_POWER_ON      = 8'h01,
    PMU_POWER_OFF     = 8'h02,
    PMU_DVFS_SET      = 8'h03,
    PMU_LOW_POWER     = 8'h04,
    PMU_SLEEP         = 8'h05,
    PMU_WAKEUP        = 8'h06,
    PMU_PROTECT       = 8'h07,
    PMU_UNPROTECT     = 8'h08
} pmu_op_type_e;

typedef enum bit[7:0] {
    PMU_ERR_NONE       = 8'h00,
    PMU_ERR_POWER      = 8'hE1,
    PMU_ERR_PROTECTION = 8'hE2,
    PMU_ERR_TIMEOUT    = 8'hE3,
    PMU_ERR_INVALID    = 8'hE4
} pmu_status_e;

class pmu_seq_item extends uvm_sequence_item;
    `uvm_object_utils(pmu_seq_item)

    rand pmu_op_type_e  op_type;
    rand bit[2:0]       power_domain;
    rand bit[7:0]       voltage_level;
    rand bit[15:0]      frequency;
    rand bit[31:0]      timeout_val;
    bit                 protect_enable;
    bit                 status;
    string              op_name;

    constraint valid_domain {
        power_domain inside {[0:4]};
    }

    constraint valid_voltage {
        voltage_level inside {[0:3]};
    }

    constraint valid_freq {
        frequency inside {500, 1000, 1500, 2000};
    }

    function new(string name = "pmu_seq_item");
        super.new(name);
        op_name = op_type.name();
    endfunction

    function string convert2string();
        return $sformatf("op_type=%s domain=%0d voltage=%0d freq=%0d status=%0d",
            op_name, power_domain, voltage_level, frequency, status);
    endfunction
endclass

`endif
