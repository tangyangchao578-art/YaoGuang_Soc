class mem_ctrl_basic_seq extends uvm_sequence #(mem_ctrl_transaction);
    `uvm_object_utils(mem_ctrl_basic_seq)
    
    function new(string name = "mem_ctrl_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(1000) begin
            mem_ctrl_transaction tr;
            tr = mem_ctrl_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class mem_ctrl_ddr_seq extends uvm_sequence #(mem_ctrl_transaction);
    `uvm_object_utils(mem_ctrl_ddr_seq)
    
    function new(string name = "mem_ctrl_ddr_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 1000; i++) begin
            mem_ctrl_transaction tr;
            tr = mem_ctrl_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class mem_ctrl_burst_seq extends uvm_sequence #(mem_ctrl_transaction);
    `uvm_object_utils(mem_ctrl_burst_seq)
    
    function new(string name = "mem_ctrl_burst_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 100; i++) begin
            mem_ctrl_transaction tr;
            tr = mem_ctrl_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class mem_ctrl_error_seq extends uvm_sequence #(mem_ctrl_transaction);
    `uvm_object_utils(mem_ctrl_error_seq)
    
    function new(string name = "mem_ctrl_error_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            mem_ctrl_transaction tr;
            tr = mem_ctrl_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 0; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class mem_ctrl_performance_seq extends uvm_sequence #(mem_ctrl_transaction);
    `uvm_object_utils(mem_ctrl_performance_seq)
    
    function new(string name = "mem_ctrl_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        time start_time, end_time;
        
        start_time = $time;
        
        repeat(100000) begin
            mem_ctrl_transaction tr;
            tr = mem_ctrl_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        `uvm_info("PERF", $sformatf("Memory Controller Throughput Test Complete in %0t ns", end_time - start_time), UVM_LOW)
    endtask
endclass
