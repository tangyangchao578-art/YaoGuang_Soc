class display_basic_seq extends uvm_sequence #(display_transaction);
    `uvm_object_utils(display_basic_seq)
    
    function new(string name = "display_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(100) begin
            display_transaction tr;
            tr = display_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class display_resolution_seq extends uvm_sequence #(display_transaction);
    `uvm_object_utils(display_resolution_seq)
    
    function new(string name = "display_resolution_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 100; i++) begin
            display_transaction tr;
            tr = display_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class display_error_seq extends uvm_sequence #(display_transaction);
    `uvm_object_utils(display_error_seq)
    
    function new(string name = "display_error_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            display_transaction tr;
            tr = display_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 0; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class display_performance_seq extends uvm_sequence #(display_transaction);
    `uvm_object_utils(display_performance_seq)
    
    function new(string name = "display_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        time start_time, end_time;
        
        start_time = $time;
        
        repeat(100000) begin
            display_transaction tr;
            tr = display_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        `uvm_info("PERF", $sformatf("Display Throughput Test Complete in %0t ns", end_time - start_time), UVM_LOW)
    endtask
endclass
