`ifndef PMU_TESTS_SV
`define PMU_TESTS_SV

class pmu_base_test extends dv_base_test;
    `uvm_component_utils(pmu_base_test)

    pmu_env       env;
    pmu_env_config cfg;

    function new(string name = "pmu_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = new();
        cfg.is_active = 1;
        cfg.has_scoreboard = 1;
        cfg.has_coverage = 1;
        uvm_config_db#(pmu_env_config)::set(this, "*", "pmu_env_config", cfg);
        env = pmu_env::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1000;
        phase.drop_objection(this);
    endtask
endclass

class pmu_sanity_test extends pmu_base_test;
    `uvm_component_utils(pmu_sanity_test)

    pmu_power_seq power_seq;

    function new(string name = "pmu_sanity_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        power_seq = pmu_power_seq::type_id::create("power_seq");
        power_seq.num_transactions = 50;
        power_seq.start(env.agent.sequencer);
        #500;
        phase.drop_objection(this);
    endtask
endclass

class pmu_power_test extends pmu_base_test;
    `uvm_component_utils(pmu_power_test)

    pmu_power_on_seq   on_seq;
    pmu_power_off_seq  off_seq;
    pmu_all_power_seq  all_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        on_seq = pmu_power_on_seq::type_id::create("on_seq");
        off_seq = pmu_power_off_seq::type_id::create("off_seq");
        all_seq = pmu_all_power_seq::type_id::create("all_seq");

        fork
            on_seq.start(env.agent.sequencer);
            off_seq.start(env.agent.sequencer);
            all_seq.start(env.agent.sequencer);
        join

        #1000;
        phase.drop_objection(this);
    endtask
endclass

class pmu_dvfs_test extends pmu_base_test;
    `uvm_component_utils(pmu_dvfs_test)

    pmu_dvfs_seq       dvfs_seq;
    pmu_dvfs_sweep_seq sweep_seq;
    pmu_dvfs_transition_seq trans_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        dvfs_seq = pmu_dvfs_seq::type_id::create("dvfs_seq");
        sweep_seq = pmu_dvfs_sweep_seq::type_id::create("sweep_seq");
        trans_seq = pmu_dvfs_transition_seq::type_id::create("trans_seq");

        fork
            dvfs_seq.start(env.agent.sequencer);
            sweep_seq.start(env.agent.sequencer);
            trans_seq.start(env.agent.sequencer);
        join

        #2000;
        phase.drop_objection(this);
    endtask
endclass

class pmu_low_power_test extends pmu_base_test;
    `uvm_component_utils(pmu_low_power_test)

    pmu_low_power_seq     low_seq;
    pmu_sleep_seq         sleep_seq;
    pmu_wakeup_seq        wakeup_seq;
    pmu_sleep_wakeup_seq  sleep_wakeup_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        low_seq = pmu_low_power_seq::type_id::create("low_seq");
        sleep_seq = pmu_sleep_seq::type_id::create("sleep_seq");
        wakeup_seq = pmu_wakeup_seq::type_id::create("wakeup_seq");
        sleep_wakeup_seq = pmu_sleep_wakeup_seq::type_id::create("sleep_wakeup_seq");

        fork
            low_seq.start(env.agent.sequencer);
            sleep_seq.start(env.agent.sequencer);
            wakeup_seq.start(env.agent.sequencer);
            sleep_wakeup_seq.start(env.agent.sequencer);
        join

        #2000;
        phase.drop_objection(this);
    endtask
endclass

class pmu_protection_test extends pmu_base_test;
    `uvm_component_utils(pmu_protection_test)

    pmu_protection_seq           prot_seq;
    pmu_protect_seq              protect_seq;
    pmu_unprotect_seq            unprotect_seq;
    pmu_protection_violation_seq violation_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        prot_seq = pmu_protection_seq::type_id::create("prot_seq");
        protect_seq = pmu_protect_seq::type_id::create("protect_seq");
        unprotect_seq = pmu_unprotect_seq::type_id::create("unprotect_seq");
        violation_seq = pmu_protection_violation_seq::type_id::create("violation_seq");

        fork
            prot_seq.start(env.agent.sequencer);
            protect_seq.start(env.agent.sequencer);
            unprotect_seq.start(env.agent.sequencer);
            violation_seq.start(env.agent.sequencer);
        join

        #2000;
        phase.drop_objection(this);
    endtask
endclass

`endif
