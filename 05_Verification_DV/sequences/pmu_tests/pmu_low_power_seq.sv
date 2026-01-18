`ifndef PMU_LOW_POWER_SEQ_SV
`define PMU_LOW_POWER_SEQ_SV

class pmu_low_power_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_low_power_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    constraint trans_cons {
        num_transactions inside {[20:50]};
    }

    function new(string name = "pmu_low_power_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = $random() % 2 ? PMU_LOW_POWER : PMU_SLEEP;
            req.power_domain = power_domain;
            req.timeout_val  = $urandom_range(100, 10000);
            finish_item(req);
        end
    endtask
endclass

class pmu_sleep_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_sleep_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;
    rand bit[31:0] sleep_time;

    function new(string name = "pmu_sleep_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_SLEEP;
            req.power_domain = power_domain;
            req.timeout_val  = sleep_time;
            finish_item(req);
        end
    endtask
endclass

class pmu_wakeup_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_wakeup_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    function new(string name = "pmu_wakeup_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_WAKEUP;
            req.power_domain = power_domain;
            finish_item(req);
        end
    endtask
endclass

class pmu_sleep_wakeup_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_sleep_wakeup_seq)

    int       num_cycles;
    bit[2:0]  power_domain;

    function new(string name = "pmu_sleep_wakeup_seq");
        super.new(name);
        num_cycles = 20;
    endfunction

    task body();
        for(int c = 0; c < num_cycles; c++) begin
            pmu_seq_item sleep_req;
            sleep_req = pmu_seq_item::type_id::create("sleep_req");
            start_item(sleep_req);
            sleep_req.op_type      = PMU_SLEEP;
            sleep_req.power_domain = power_domain;
            sleep_req.timeout_val  = $urandom_range(100, 1000);
            finish_item(sleep_req);

            pmu_seq_item wakeup_req;
            wakeup_req = pmu_seq_item::type_id::create("wakeup_req");
            start_item(wakeup_req);
            wakeup_req.op_type      = PMU_WAKEUP;
            wakeup_req.power_domain = power_domain;
            finish_item(wakeup_req);
        end
    endtask
endclass

`endif
