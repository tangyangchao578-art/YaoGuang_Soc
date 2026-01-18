//==============================================================================
// File: coverage_infra.sv
// Description: YaoGuang SoC 统一覆盖率收集基础设施
//              Unified Coverage Infrastructure for YaoGuang SoC DV Verification
// Author: YaoGuang DV Team
// Date: 2026-01-18
// Version: 1.0
//==============================================================================

`ifndef COVERAGE_INFRA_SV
`define COVERAGE_INFRA_SV

//------------------------------------------------------------------------------
// Coverage Configuration Class
//------------------------------------------------------------------------------
class coverage_config;
    string      coverage_name;
    bit         is_enabled = 1;
    bit         is_excluded = 0;
    real        target覆盖率 = 95.0;
    string      filter_mode = "include";  // include/exclude
    string      filter_patterns[$];
    
    `uvm_object_utils_begin(coverage_config)
        `uvm_field_string(coverage_name, UVM_DEFAULT)
        `uvm_field_int(is_enabled, UVM_DEFAULT)
        `uvm_field_int(is_enabled, UVM_DEFAULT)
        `uvm_field_real(target覆盖率, UVM_DEFAULT)
        `uvm_field_string(filter_mode, UVM_DEFAULT)
        `uvm_field_string_array(filter_patterns, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "coverage_config");
        super.new(name);
    endfunction
    
    function bit is_covered(string item);
        if (!is_enabled) return 0;
        if (is_excluded) return 0;
        
        foreach (filter_patterns[i]) begin
            if (filter_mode == "include") begin
                if (!uvm_re_match(filter_patterns[i], item)) return 1;
            end else begin
                if (!uvm_re_match(filter_patterns[i], item)) return 0;
            end
        end
        
        return (filter_mode == "include") ? 0 : 1;
    endfunction
endclass

//------------------------------------------------------------------------------
// Coverage Item Base Class
//------------------------------------------------------------------------------
virtual class coverage_item_base extends uvm_subscriber #(uvm_sequence_item);
    protected string                  name;
    protected coverage_config         cfg;
    protected bit                     initialized = 0;
    protected real                    current覆盖率 = 0.0;
    protected int                     total_bins = 0;
    protected int                     covered_bins = 0;
    
    `uvm_object_utils_begin(coverage_item_base)
        `uvm_field_string(name, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "coverage_item_base");
        super.new(name);
        this.name = name;
    endfunction
    
    function void set_config(coverage_config cfg);
        this.cfg = cfg;
    endfunction
    
    function coverage_config get_config();
        return cfg;
    endfunction
    
    function void build();
        `uvm_info(get_name(), $sformatf("Building coverage item: %s", name), UVM_LOW)
        initialize();
        initialized = 1;
    endfunction
    
    virtual function void initialize();
        // 子类实现
    endfunction
    
    virtual function void sample(uvm_sequence_item item);
        // 子类实现
    endfunction
    
    virtual function void sample();
        // 子类实现
    endfunction
    
    virtual function void reset();
        // 子类实现
    endfunction
    
    virtual function real get_coverage();
        return current覆盖率;
    endfunction
    
    virtual function int get_covered_bins();
        return covered_bins;
    endfunction
    
    virtual function int get_total_bins();
        return total_bins;
    endfunction
    
    virtual function bit is_goal_reached();
        return (current覆盖率 >= cfg.target覆盖率);
    endfunction
    
    virtual function string get_name();
        return name;
    endfunction
    
    virtual function void display_stats(uvm_printer printer = null);
        if (printer == null) begin
            printer = new();
        end
        
        `uvm_info(get_name(), $sformatf("Coverage: %0.2f%% (%0d/%0d bins)", 
                                        current覆盖率, covered_bins, total_bins), UVM_LOW)
    endfunction
endclass

//------------------------------------------------------------------------------
// Functional Coverage Wrapper
//------------------------------------------------------------------------------
class functional_coverage_wrapper extends coverage_item_base;
    covergroup                             cg;
    protected string                       cg_name;
    protected int                          num_samples = 0;
    
    `uvm_object_utils_begin(functional_coverage_wrapper)
        `uvm_field_string(cg_name, UVM_DEFAULT)
        `uvm_field_int(num_samples, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "functional_coverage_wrapper");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        cg = new();
        total_bins = cg.get_num_bins();
        `uvm_info(get_name(), $sformatf("Initialized functional coverage: %s with %0d bins", 
                                        cg_name, total_bins), UVM_LOW)
    endfunction
    
    virtual function void sample(uvm_sequence_item item);
        if (!initialized || !cfg.is_enabled) return;
        cg.sample();
        num_samples++;
        update_coverage();
    endfunction
    
    virtual function void sample();
        if (!initialized || !cfg.is_enabled) return;
        cg.sample();
        num_samples++;
        update_coverage();
    endfunction
    
    protected virtual function void update_coverage();
        covered_bins = cg.get_covered_bins();
        if (total_bins > 0) begin
            current覆盖率 = (covered_bins * 100.0) / total_bins;
        end
    endfunction
    
    virtual function void reset();
        cg.start();
        cg.sample();
        cg.stop();
        num_samples = 0;
        update_coverage();
    endfunction
    
    virtual function void display_stats(uvm_printer printer = null);
        super.display_stats(printer);
        `uvm_info(get_name(), $sformatf("Samples: %0d", num_samples), UVM_LOW)
    endfunction
endclass

//------------------------------------------------------------------------------
// Code Coverage Wrapper
//------------------------------------------------------------------------------
class code_coverage_wrapper extends coverage_item_base;
    protected string                       coverage_type;
    protected int                          hit_count = 0;
    protected int                          miss_count = 0;
    
    `uvm_object_utils_begin(code_coverage_wrapper)
        `uvm_field_string(coverage_type, UVM_DEFAULT)
        `uvm_field_int(hit_count, UVM_DEFAULT)
        `uvm_field_int(miss_count, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "code_coverage_wrapper");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        // 代码覆盖率由仿真器自动收集
        // 这里只提供接口
        `uvm_info(get_name(), $sformatf("Initializing code coverage: %s", coverage_type), UVM_LOW)
    endfunction
    
    virtual function void sample(uvm_sequence_item item);
        // 代码覆盖率由仿真器自动采样
        hit_count++;
        update_coverage();
    endfunction
    
    protected virtual function void update_coverage();
        if ((hit_count + miss_count) > 0) begin
            current覆盖率 = (hit_count * 100.0) / (hit_count + miss_count);
        end
    endfunction
endclass

//------------------------------------------------------------------------------
// Toggle Coverage Wrapper
//------------------------------------------------------------------------------
class toggle_coverage_wrapper extends coverage_item_base;
    protected int                          toggle_count = 0;
    protected int                          total_signals = 0;
    protected int                          covered_signals = 0;
    
    `uvm_object_utils_begin(toggle_coverage_wrapper)
        `uvm_field_int(toggle_count, UVM_DEFAULT)
        `uvm_field_int(total_signals, UVM_DEFAULT)
        `uvm_field_int(covered_signals, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "toggle_coverage_wrapper");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        `uvm_info(get_name(), "Initializing toggle coverage", UVM_LOW)
    endfunction
    
    virtual function void sample(uvm_sequence_item item);
        toggle_count++;
        update_coverage();
    endfunction
    
    protected virtual function void update_coverage();
        if (total_signals > 0) begin
            current覆盖率 = (covered_signals * 100.0) / total_signals;
        end
    endfunction
endclass

//------------------------------------------------------------------------------
// Assertion Coverage Wrapper
//------------------------------------------------------------------------------
class assertion_coverage_wrapper extends coverage_item_base;
    protected int                          assertion_count = 0;
    protected int                          passed_assertions = 0;
    protected int                          failed_assertions = 0;
    protected int                          vacuous_assertions = 0;
    
    `uvm_object_utils_begin(assertion_coverage_wrapper)
        `uvm_field_int(assertion_count, UVM_DEFAULT)
        `uvm_field_int(passed_assertions, UVM_DEFAULT)
        `uvm_field_int(failed_assertions, UVM_DEFAULT)
        `uvm_field_int(vacuous_assertions, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "assertion_coverage_wrapper");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        `uvm_info(get_name(), "Initializing assertion coverage", UVM_LOW)
    endfunction
    
    virtual function void sample(uvm_sequence_item item);
        assertion_count++;
        update_coverage();
    endfunction
    
    function void sample_pass();
        passed_assertions++;
        update_coverage();
    endfunction
    
    function void sample_fail();
        failed_assertions++;
        update_coverage();
    endfunction
    
    function void sample_vacuous();
        vacuous_assertions++;
        update_coverage();
    endfunction
    
    protected virtual function void update_coverage();
        if (assertion_count > 0) begin
            current覆盖率 = (passed_assertions * 100.0) / assertion_count;
        end
    endfunction
    
    virtual function void display_stats(uvm_printer printer = null);
        super.display_stats(printer);
        `uvm_info(get_name(), $sformatf("Passed: %0d, Failed: %0d, Vacuous: %0d",
                                        passed_assertions, failed_assertions, vacuous_assertions), UVM_LOW)
    endfunction
endclass

//------------------------------------------------------------------------------
// FSM Coverage Wrapper
//------------------------------------------------------------------------------
class fsm_coverage_wrapper extends coverage_item_base;
    protected int                          state_count = 0;
    protected int                          transition_count = 0;
    protected int                          covered_states = 0;
    protected int                          covered_transitions = 0;
    
    `uvm_object_utils_begin(fsm_coverage_wrapper)
        `uvm_field_int(state_count, UVM_DEFAULT)
        `uvm_field_int(transition_count, UVM_DEFAULT)
        `uvm_field_int(covered_states, UVM_DEFAULT)
        `uvm_field_int(covered_transitions, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "fsm_coverage_wrapper");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        `uvm_info(get_name(), "Initializing FSM coverage", UVM_LOW)
    endfunction
    
    virtual function void sample(uvm_sequence_item item);
        transition_count++;
        update_coverage();
    endfunction
    
    function void sample_state(string state);
        state_count++;
        update_coverage();
    endfunction
    
    function void sample_transition(string from_state, string to_state);
        transition_count++;
        update_coverage();
    endfunction
    
    protected virtual function void update_coverage();
        if (state_count > 0) begin
            current覆盖率 = ((covered_states + covered_transitions) * 100.0) / 
                           (state_count + transition_count);
        end
    endfunction
endclass

//------------------------------------------------------------------------------
// Unified Coverage Collector
//------------------------------------------------------------------------------
class coverage_collector extends uvm_component;
    protected string                           name;
    protected coverage_config                   cfg;
    protected coverage_item_base                coverage_items[$];
    protected bit                               is_running = 0;
    protected real                              overall_coverage = 0.0;
    protected real                              last_coverage = 0.0;
    protected real                              coverage_delta = 0.0;
    
    // 覆盖率统计
    protected int                               total_goals = 0;
    protected int                               achieved_goals = 0;
    protected real                              average_coverage = 0.0;
    
    // 事件
    uvm_event                                   coverage_updated_event;
    uvm_event                                   goal_reached_event;
    uvm_event                                   coverage_stalled_event;
    
    // 定时器
    protected real                              last_update_time = 0.0;
    protected real                              stall_threshold = 5.0;  // 百分比
    protected real                              stall_timeout = 300.0;   // 秒
    
    `uvm_component_utils_begin(coverage_collector)
        `uvm_field_string(name, UVM_DEFAULT)
        `uvm_field_int(overall_coverage, UVM_LOW)
    `uvm_component_utils_end
    
    function new(string name = "coverage_collector", uvm_component parent = null);
        super.new(name, parent);
        this.name = name;
        coverage_updated_event = new("coverage_updated_event");
        goal_reached_event = new("goal_reached_event");
        coverage_stalled_event = new("coverage_stalled_event");
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // 获取覆盖率配置
        if (uvm_config_db #(coverage_config)::get(this, "", "coverage_config", cfg)) begin
            `uvm_info(get_name(), "Got coverage config from DB", UVM_LOW)
        end else begin
            cfg = coverage_config::type_id::create("default_coverage_config");
            `uvm_info(get_name(), "Created default coverage config", UVM_LOW)
        end
        
        build_coverage_items();
    endfunction
    
    virtual function void build_coverage_items();
        `uvm_info(get_name(), "Building coverage items", UVM_LOW)
        
        // 子类实现具体的coverage items
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // 注册到全局覆盖率管理器
        coverage_manager::get().register_collector(this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        is_running = 1;
        last_update_time = $realtime();
        
        fork
            monitor_coverage_progress();
            sample_coverage();
        join_none
    endtask
    
    protected virtual task monitor_coverage_progress();
        real current_time;
        real time_elapsed;
        
        forever begin
            #100ns;
            
            current_time = $realtime();
            time_elapsed = current_time - last_update_time;
            
            // 检查覆盖率是否停滞
            coverage_delta = overall_coverage - last_coverage;
            
            if (coverage_delta < stall_threshold && time_elapsed > stall_timeout) begin
                `uvm_warning(get_name(), $sformatf("Coverage stalled: delta=%0.2f%% in %0.1fs",
                                                   coverage_delta, time_elapsed))
                coverage_stalled_event.trigger();
            end
            
            // 更新统计
            if (coverage_delta >= stall_threshold) begin
                last_update_time = current_time;
                last_coverage = overall_coverage;
            end
        end
    endtask
    
    protected virtual task sample_coverage();
        forever begin
            #1us;
            
            if (!is_running) continue;
            
            // 采样所有coverage items
            foreach (coverage_items[i]) begin
                if (coverage_items[i].is_enabled()) begin
                    // 采样由具体的coverage item实现
                end
            end
            
            // 计算总体覆盖率
            calculate_overall_coverage();
            
            // 检查目标达成
            check_goals();
            
            // 触发事件
            coverage_updated_event.trigger();
        end
    endtask
    
    virtual function void calculate_overall_coverage();
        real total_weight = 0.0;
        real weighted_sum = 0.0;
        
        foreach (coverage_items[i]) begin
            if (coverage_items[i].is_enabled()) begin
                real weight = get_coverage_weight(coverage_items[i]);
                total_weight += weight;
                weighted_sum += coverage_items[i].get_coverage() * weight;
            end
        end
        
        if (total_weight > 0) begin
            overall_coverage = weighted_sum / total_weight;
        end
        
        average_coverage = overall_coverage;
    endfunction
    
    virtual function real get_coverage_weight(coverage_item_base item);
        return 1.0;  // 默认权重
    endfunction
    
    virtual function void check_goals();
        achieved_goals = 0;
        total_goals = 0;
        
        foreach (coverage_items[i]) begin
            total_goals++;
            if (coverage_items[i].is_goal_reached()) begin
                achieved_goals++;
            end
        end
        
        if (achieved_goals == total_goals && total_goals > 0) begin
            `uvm_info(get_name(), $sformatf("All coverage goals reached: %0.2f%%", overall_coverage), UVM_LOW)
            goal_reached_event.trigger();
        end
    endfunction
    
    virtual function void add_coverage_item(coverage_item_base item);
        item.set_config(cfg);
        item.build();
        coverage_items.push_back(item);
    endfunction
    
    virtual function void remove_coverage_item(string name);
        foreach (coverage_items[i]) begin
            if (coverage_items[i].get_name() == name) begin
                coverage_items.delete(i);
                break;
            end
        end
    endfunction
    
    virtual function void reset();
        foreach (coverage_items[i]) begin
            coverage_items[i].reset();
        end
        calculate_overall_coverage();
    endfunction
    
    virtual function void clear();
        foreach (coverage_items[i]) begin
            coverage_items[i].reset();
        end
        overall_coverage = 0.0;
        calculate_overall_coverage();
    endfunction
    
    virtual function real get_overall_coverage();
        return overall_coverage;
    endfunction
    
    virtual function bit is_goal_reached();
        return (overall_coverage >= cfg.target覆盖率);
    endfunction
    
    virtual function void print_coverage_report(uvm_printer printer = null);
        if (printer == null) begin
            printer = new();
        end
        
        `uvm_info(get_name(), "=================================================", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Coverage Report: %s", name), UVM_LOW)
        `uvm_info(get_name(), "=================================================", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Overall Coverage: %0.2f%%", overall_coverage), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Goals: %0d/%0d achieved", achieved_goals, total_goals), UVM_LOW)
        `uvm_info(get_name(), "-------------------------------------------------", UVM_LOW)
        
        foreach (coverage_items[i]) begin
            coverage_items[i].display_stats(printer);
        end
        
        `uvm_info(get_name(), "=================================================", UVM_LOW)
    endfunction
    
    virtual function void get_coverage_report(ref coverage_report_t report);
        report.name = name;
        report.overall_coverage = overall_coverage;
        report.total_goals = total_goals;
        report.achieved_goals = achieved_goals;
        report.items = new[coverage_items.size()];
        
        foreach (coverage_items[i]) begin
            report.items[i].name = coverage_items[i].get_name();
            report.items[i].coverage = coverage_items[i].get_coverage();
            report.items[i].covered_bins = coverage_items[i].get_covered_bins();
            report.items[i].total_bins = coverage_items[i].get_total_bins();
            report.items[i].goal_reached = coverage_items[i].is_goal_reached();
        end
    endfunction
    
    virtual function void stop_phase(uvm_phase phase);
        is_running = 0;
        print_coverage_report();
        super.stop_phase(phase);
    endfunction
endclass

//------------------------------------------------------------------------------
// Global Coverage Manager
//------------------------------------------------------------------------------
class coverage_manager extends uvm_object;
    protected static coverage_manager               singleton;
    protected coverage_collector                    collectors[$];
    protected coverage_config                       global_cfg;
    protected string                                report_dir = "coverage_reports";
    protected string                                db_file = "coverage.db";
    
    `uvm_object_utils_begin(coverage_manager)
        `uvm_field_string(report_dir, UVM_DEFAULT)
        `uvm_field_string(db_file, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "coverage_manager");
        super.new(name);
        global_cfg = coverage_config::type_id::create("global_coverage_config");
        report_dir = "coverage_reports";
    endfunction
    
    static function coverage_manager get();
        if (singleton == null) begin
            singleton = new();
        end
        return singleton;
    endfunction
    
    function void register_collector(coverage_collector collector);
        collectors.push_back(collector);
    endfunction
    
    function void unregister_collector(coverage_collector collector);
        foreach (collectors[i]) begin
            if (collectors[i] == collector) begin
                collectors.delete(i);
                break;
            end
        end
    endfunction
    
    function void reset_all();
        foreach (collectors[i]) begin
            collectors[i].reset();
        end
    endfunction
    
    function void clear_all();
        foreach (collectors[i]) begin
            collectors[i].clear();
        end
    endfunction
    
    function real get_overall_coverage();
        real total = 0.0;
        real count = 0.0;
        
        foreach (collectors[i]) begin
            total += collectors[i].get_overall_coverage();
            count++;
        end
        
        return (count > 0) ? (total / count) : 0.0;
    endfunction
    
    function bit all_goals_reached();
        foreach (collectors[i]) begin
            if (!collectors[i].is_goal_reached()) begin
                return 0;
            end
        end
        return 1;
    endfunction
    
    function void generate_report(string filename = "");
        string report_file;
        
        if (filename == "") begin
            report_file = $sformatf("%s/coverage_report_%0t.txt", report_dir, $time);
        end else begin
            report_file = filename;
        end
        
        `uvm_info("COVERAGE_MGR", $sformatf("Generating coverage report: %s", report_file), UVM_LOW)
        
        // 打印报告到文件
        foreach (collectors[i]) begin
            collectors[i].print_coverage_report();
        end
        
        `uvm_info("COVERAGE_MGR", $sformatf("Overall Coverage: %0.2f%%", get_overall_coverage()), UVM_LOW)
    endfunction
    
    function void export_coverage_db(string format = "urg");
        string db_path = $sformatf("%s/%s", report_dir, db_file);
        
        `uvm_info("COVERAGE_MGR", $sformatf("Exporting coverage DB: %s", db_path), UVM_LOW)
        
        // 调用仿真器的覆盖率导出功能
        // $coverage_save(db_path, ...);
    endfunction
    
    function void merge_coverage_db(string input_dbs[$], string output_db);
        `uvm_info("COVERAGE_MGR", $sformatf("Merging coverage DBs from %0d sources", input_dbs.size()), UVM_LOW)
        
        // 实现覆盖率合并逻辑
    endfunction
    
    function void set_report_dir(string dir);
        report_dir = dir;
        `uvm_info("COVERAGE_MGR", $sformatf("Set report directory: %s", report_dir), UVM_LOW)
    endfunction
    
    function void configure_thresholds(coverage_config cfg);
        global_cfg = cfg;
    endfunction
endclass

//------------------------------------------------------------------------------
// Coverage Threshold Checker
//------------------------------------------------------------------------------
class coverage_threshold_checker extends uvm_component;
    coverage_config         thresholds;
    uvm_event               threshold_violated_event;
    string                  violation_modules[$];
    
    `uvm_component_utils_begin(coverage_threshold_checker)
        `uvm_field_object(thresholds, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "coverage_threshold_checker", uvm_component parent = null);
        super.new(name, parent);
        thresholds = coverage_config::type_id::create("thresholds");
        threshold_violated_event = new("threshold_violated_event");
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (uvm_config_db #(coverage_config)::get(this, "", "threshold_config", thresholds)) begin
            `uvm_info(get_name(), "Loaded threshold config", UVM_LOW)
        end
    endfunction
    
    virtual function void check_coverage(coverage_collector collector);
        real coverage = collector.get_overall_coverage();
        real threshold = thresholds.target覆盖率;
        
        if (coverage < threshold) begin
            `uvm_warning(get_name(), $sformatf("Coverage threshold violated for %s: %0.2f%% < %0.2f%%",
                                               collector.get_name(), coverage, threshold))
            violation_modules.push_back(collector.get_name());
            threshold_violated_event.trigger();
        end else begin
            `uvm_info(get_name(), $sformatf("Coverage goal met for %s: %0.2f%% >= %0.2f%%",
                                            collector.get_name(), coverage, threshold), UVM_LOW)
        end
    endfunction
    
    virtual function void check_all();
        coverage_manager mgr = coverage_manager::get();
        
        violation_modules.delete();
        
        // mgr.reset_all()被调用后，收集器被注册
        // 这里需要遍历所有收集器
    endfunction
    
    virtual function bit is_pass();
        return (violation_modules.size() == 0);
    endfunction
endclass

//------------------------------------------------------------------------------
// Coverage HTML Report Generator
//------------------------------------------------------------------------------
class coverage_html_report_gen extends uvm_component;
    protected string                          output_file;
    protected string                          title = "YaoGuang SoC Coverage Report";
    protected real                            overall_coverage = 0.0;
    protected coverage_report_t               reports[$];
    
    `uvm_component_utils_begin(coverage_html_report_gen)
        `uvm_field_string(output_file, UVM_DEFAULT)
        `uvm_field_string(title, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "coverage_html_report_gen", uvm_component parent = null);
        super.new(name, parent);
        output_file = "coverage_report.html";
    endfunction
    
    virtual function void generate(coverage_report_t reports[$], string filename = "");
        if (filename != "") begin
            output_file = filename;
        end
        
        this.reports = reports;
        
        // 计算总体覆盖率
        overall_coverage = 0.0;
        foreach (reports[i]) begin
            overall_coverage += reports[i].overall_coverage;
        end
        overall_coverage /= reports.size();
        
        write_html_header();
        write_html_body();
        write_html_footer();
        
        `uvm_info(get_name(), $sformatf("Generated HTML coverage report: %s", output_file), UVM_LOW)
    endfunction
    
    protected virtual function void write_html_header();
        // 生成HTML头部
    endfunction
    
    protected virtual function void write_html_body();
        // 生成HTML主体
    endfunction
    
    protected virtual function void write_html_footer();
        // 生成HTML尾部
    endfunction
endclass

//------------------------------------------------------------------------------
// Coverage Data Types
//------------------------------------------------------------------------------
typedef struct {
    string          name;
    real            coverage;
    int             covered_bins;
    int             total_bins;
    bit             goal_reached;
} coverage_report_item_t;

typedef struct {
    string                      name;
    real                        overall_coverage;
    int                         total_goals;
    int                         achieved_goals;
    coverage_report_item_t      items[];
} coverage_report_t;

//------------------------------------------------------------------------------
// Coverage Database Interface
//------------------------------------------------------------------------------
class coverage_db_interface extends uvm_object;
    protected string              db_path;
    protected int                 db_handle;
    
    `uvm_object_utils_begin(coverage_db_interface)
        `uvm_field_string(db_path, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "coverage_db_interface");
        super.new(name);
    endfunction
    
    virtual function void open(string path);
        db_path = path;
        `uvm_info(get_name(), $sformatf("Opening coverage DB: %s", db_path), UVM_LOW)
    endfunction
    
    virtual function void close();
        `uvm_info(get_name(), $sformatf("Closing coverage DB: %s", db_path), UVM_LOW)
    endfunction
    
    virtual function void save_coverage(coverage_report_t report);
        // 保存覆盖率数据到数据库
    endfunction
    
    virtual function void load_coverage(string module, ref coverage_report_t report);
        // 从数据库加载覆盖率数据
    endfunction
    
    virtual function void query_trends(string module, int days, ref real trends[$]);
        // 查询覆盖率趋势
    endfunction
endclass

//==============================================================================
// Utility Functions and Tasks
//==============================================================================

//------------------------------------------------------------------------------
// Coverage Sample Task
//------------------------------------------------------------------------------
task sample_coverage_coverage_item(coverage_item_base item, uvm_sequence_item trans = null);
    if (item.is_enabled()) begin
        if (trans != null) begin
            item.sample(trans);
        end else begin
            item.sample();
        end
    end
endtask

//------------------------------------------------------------------------------
// Wait for Coverage Goal Task
//------------------------------------------------------------------------------
task wait_for_coverage_goal(coverage_collector collector, real target = 95.0, int timeout = 0);
    real current;
    int timeout_count = 0;
    int max_iterations = (timeout > 0) ? (timeout * 1000) : 1000000;
    
    forever begin
        #1ms;
        current = collector.get_overall_coverage();
        
        `uvm_info("COVERAGE_WAIT", $sformatf("Current coverage: %0.2f%%, Target: %0.2f%%",
                                              current, target), UVM_LOW)
        
        if (current >= target) begin
            `uvm_info("COVERAGE_WAIT", "Coverage goal reached!", UVM_LOW)
            return;
        end
        
        timeout_count++;
        if (timeout_count > max_iterations) begin
            `uvm_warning("COVERAGE_WAIT", "Coverage goal timeout!")
            return;
        end
    end
endtask

//------------------------------------------------------------------------------
// Print Coverage Summary Task
//------------------------------------------------------------------------------
task print_coverage_summary(coverage_manager mgr = null);
    if (mgr == null) begin
        mgr = coverage_manager::get();
    end
    
    `uvm_info("COVERAGE_SUMMARY", "=================================================", UVM_LOW)
    `uvm_info("COVERAGE_SUMMARY", "           COVERAGE SUMMARY", UVM_LOW)
    `uvm_info("COVERAGE_SUMMARY", "=================================================", UVM_LOW)
    `uvm_info("COVERAGE_SUMMARY", $sformatf("Overall Coverage: %0.2f%%", mgr.get_overall_coverage()), UVM_LOW)
    `uvm_info("COVERAGE_SUMMARY", $sformatf("All Goals Reached: %s", 
                                              mgr.all_goals_reached() ? "YES" : "NO"), UVM_LOW)
    `uvm_info("COVERAGE_SUMMARY", "=================================================", UVM_LOW)
endtask

`endif  // COVERAGE_INFRA_SV
