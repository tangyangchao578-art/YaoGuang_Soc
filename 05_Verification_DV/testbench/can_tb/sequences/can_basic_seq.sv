class can_basic_seq extends uvm_sequence #(can_transaction);
    `uvm_object_utils(can_basic_seq)
    
    function new(string name = "can_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(100) begin
            can_transaction tr;
            tr = can_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class can_fd_seq extends uvm_sequence #(can_transaction);
    `uvm_object_utils(can_fd_seq)
    
    function new(string name = "can_fd_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 50; i++) begin
            can_transaction tr;
            tr = can_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class can_error_seq extends uvm_sequence #(can_transaction);
    `uvm_object_utils(can_error_seq)
    
    function new(string name = "can_error_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            can_transaction tr;
            tr = can_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 0; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class can_performance_seq extends uvm_sequence #(can_transaction);
    `uvm_object_utils(can_performance_seq)
    
    function new(string name = "can_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        time start_time, end_time;
        
        start_time = $time;
        
        repeat(10000) begin
            can_transaction tr;
            tr = can_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        `uvm_info("PERF", $sformatf("CAN Throughput Test Complete in %0t ns", end_time - start_time), UVM_LOW)
    endtask
endclass
