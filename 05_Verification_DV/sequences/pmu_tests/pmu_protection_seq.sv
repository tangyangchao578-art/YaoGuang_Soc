`ifndef PMU_PROTECTION_SEQ_SV
`define PMU_PROTECTION_SEQ_SV

class pmu_protection_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_protection_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    constraint trans_cons {
        num_transactions inside {[20:50]};
    }

    function new(string name = "pmu_protection_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type       = $random() % 2 ? PMU_PROTECT : PMU_UNPROTECT;
            req.power_domain  = power_domain;
            req.protect_enable = $random();
            finish_item(req);
        end
    endtask
endclass

class pmu_protect_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_protect_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    function new(string name = "pmu_protect_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_PROTECT;
            req.power_domain = power_domain;
            req.protect_enable = 1'b1;
            finish_item(req);
        end
    endtask
endclass

class pmu_unprotect_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_unprotect_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;

    function new(string name = "pmu_unprotect_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_UNPROTECT;
            req.power_domain = power_domain;
            req.protect_enable = 1'b0;
            finish_item(req);
        end
    endtask
endclass

class pmu_protection_violation_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_protection_violation_seq)

    int       num_tests;

    function new(string name = "pmu_protection_violation_seq");
        super.new(name);
        num_tests = 20;
    endfunction

    task body();
        for(int i = 0; i < num_tests; i++) begin
            pmu_seq_item protect_req;
            protect_req = pmu_seq_item::type_id::create("protect_req");
            start_item(protect_req);
            protect_req.op_type      = PMU_PROTECT;
            protect_req.power_domain = $urandom_range(0, 4);
            protect_req.protect_enable = 1'b1;
            finish_item(protect_req);

            pmu_seq_item access_req;
            access_req = pmu_seq_item::type_id::create("access_req");
            start_item(access_req);
            access_req.op_type      = PMU_POWER_OFF;
            access_req.power_domain = protect_req.power_domain;
            finish_item(access_req);
        end
    endtask
endclass

`endif
