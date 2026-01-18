`ifndef PMU_POWER_SEQ_SV
`define PMU_POWER_SEQ_SV

class pmu_power_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_power_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    constraint trans_cons {
        num_transactions inside {[20:50]};
    }

    function new(string name = "pmu_power_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = $random() % 2 ? PMU_POWER_ON : PMU_POWER_OFF;
            req.power_domain = power_domain;
            req.voltage_level = $urandom_range(0, 3);
            req.frequency    = 1000;
            finish_item(req);
        end
    endtask
endclass

class pmu_power_on_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_power_on_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    function new(string name = "pmu_power_on_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_POWER_ON;
            req.power_domain = power_domain;
            req.voltage_level = $urandom_range(0, 3);
            req.frequency    = 1000;
            finish_item(req);
        end
    endtask
endclass

class pmu_power_off_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_power_off_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    function new(string name = "pmu_power_off_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_POWER_OFF;
            req.power_domain = power_domain;
            finish_item(req);
        end
    endtask
endclass

class pmu_all_power_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_all_power_seq)

    int       num_cycles;

    function new(string name = "pmu_all_power_seq");
        super.new(name);
        num_cycles = 10;
    endfunction

    task body();
        for(int c = 0; c < num_cycles; c++) begin
            for(int d = 0; d < 5; d++) begin
                pmu_seq_item req;
                req = pmu_seq_item::type_id::create("req");
                start_item(req);
                req.op_type      = c % 2 ? PMU_POWER_ON : PMU_POWER_OFF;
                req.power_domain = d;
                req.voltage_level = $urandom_range(0, 3);
                req.frequency    = 1000;
                finish_item(req);
            end
        end
    endtask
endclass

`endif
