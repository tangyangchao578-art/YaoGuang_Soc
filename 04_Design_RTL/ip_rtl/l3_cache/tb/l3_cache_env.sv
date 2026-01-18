// ============================================================================
// Class: l3_cache_env
// Description: L3 Cache UVM验证环境
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_ENV_SV
`define L3_CACHE_ENV_SV

class l3_cache_env extends uvm_env;

    // 组件实例
    l3_cache_agent             agent;
    l3_cache_scoreboard        scoreboard;
    l3_cache_reference_model   ref_model;
    l3_cache_coverage          coverage;
    l3_cache_virtual_sequencer vsequencer;

    // 配置
    l3_cache_config            cfg;

    `uvm_component_utils(l3_cache_env)

    function new(string name = "l3_cache_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // 获取配置
        if (!uvm_config_db#(l3_cache_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG", "Cannot get cfg from config_db")
        end

        // 创建Agent
        agent = l3_cache_agent::type_id::create("agent", this);
        uvm_config_db#(l3_cache_config)::set(this, "agent", "cfg", cfg);

        // 创建Scoreboard
        scoreboard = l3_cache_scoreboard::type_id::create("scoreboard", this);

        // 创建Reference Model
        ref_model = l3_cache_reference_model::type_id::create("ref_model", this);

        // 创建Coverage
        coverage = l3_cache_coverage::type_id::create("coverage", this);

        // 创建Virtual Sequencer
        vsequencer = l3_cache_virtual_sequencer::type_id::create("vsequencer", this);
        vsequencer.cfg = cfg;
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Agent到Scoreboard连接
        agent.monitor.ap.connect(scoreboard.expected_export);
        agent.monitor.ap.connect(ref_model.port);
        ref_model.ap.connect(scoreboard.actual_export);

        // Coverage连接
        agent.monitor.ap.connect(coverage.analysis_export);

        // Sequencer连接
        vsequencer.agent_seqr = agent.sequencer;
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        // 运行主序列
        l3_cache_main_sequence seq = l3_cache_main_sequence::type_id::create("seq");
        seq.start(vsequencer);

        phase.drop_objection(this);
    endtask

    virtual function void report_phase(uvm_phase phase);
        // 打印覆盖率报告
        `uvm_info("ENV", $sformatf("Coverage: %0.2f%%", coverage.get_coverage()), UVM_LOW)
    endfunction

endclass

`endif
