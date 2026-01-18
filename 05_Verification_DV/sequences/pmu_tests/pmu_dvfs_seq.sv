`ifndef PMU_DVFS_SEQ_SV
`define PMU_DVFS_SEQ_SV

class pmu_dvfs_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_dvfs_seq)

    rand int       num_transactions;
    rand bit[2:0]  power_domain;
    rand bit[15:0] frequency;
    rand bit[7:0]  voltage_level;

    constraint trans_cons {
        num_transactions inside {[30:100]};
        frequency inside {500, 1000, 1500, 2000};
        voltage_level dist {0:/20, 1:/30, 2:/30, 3:/20};
    }

    function new(string name = "pmu_dvfs_seq");
        super.new(name);
        num_transactions = 50;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_DVFS_SET;
            req.power_domain = power_domain;
            req.frequency    = frequency;
            req.voltage_level = voltage_level;
            finish_item(req);
        end
    endtask
endclass

class pmu_dvfs_sweep_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_dvfs_sweep_seq)

    int       num_cycles;
    bit[2:0]  power_domain;

    function new(string name = "pmu_dvfs_sweep_seq");
        super.new(name);
        num_cycles = 20;
    endfunction

    task body();
        bit[15:0] freqs[] = '{500, 1000, 1500, 2000};
        bit[7:0] volts[] = '{0, 1, 2, 3};

        for(int c = 0; c < num_cycles; c++) begin
            for(int f = 0; f < freqs.size(); f++) begin
                for(int v = 0; v < volts.size(); v++) begin
                    pmu_seq_item req;
                    req = pmu_seq_item::type_id::create("req");
                    start_item(req);
                    req.op_type      = PMU_DVFS_SET;
                    req.power_domain = power_domain;
                    req.frequency    = freqs[f];
                    req.voltage_level = volts[v];
                    finish_item(req);
                end
            end
        end
    endtask
endclass

class pmu_dvfs_transition_seq extends uvm_sequence#(pmu_seq_item);
    `uvm_object_utils(pmu_dvfs_transition_seq)

    int       num_transitions;
    bit[2:0]  power_domain;

    function new(string name = "pmu_dvfs_transition_seq");
        super.new(name);
        num_transitions = 100;
    endfunction

    task body();
        for(int i = 0; i < num_transitions; i++) begin
            pmu_seq_item req;
            req = pmu_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = PMU_DVFS_SET;
            req.power_domain = power_domain;
            req.frequency    = $urandom_range(500, 2000);
            req.voltage_level = $urandom_range(0, 3);
            finish_item(req);
        end
    endtask
endclass

`endif
