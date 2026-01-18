class crypto_basic_seq extends uvm_sequence #(crypto_transaction);
    `uvm_object_utils(crypto_basic_seq)
    
    function new(string name = "crypto_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(100) begin
            crypto_transaction tr;
            tr = crypto_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class crypto_aes_seq extends uvm_sequence #(crypto_transaction);
    `uvm_object_utils(crypto_aes_seq)
    
    function new(string name = "crypto_aes_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 50; i++) begin
            crypto_transaction tr;
            tr = crypto_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; algorithm == 0; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class crypto_sha_seq extends uvm_sequence #(crypto_transaction);
    `uvm_object_utils(crypto_sha_seq)
    
    function new(string name = "crypto_sha_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 50; i++) begin
            crypto_transaction tr;
            tr = crypto_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 1; algorithm == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class crypto_error_seq extends uvm_sequence #(crypto_transaction);
    `uvm_object_utils(crypto_error_seq)
    
    function new(string name = "crypto_error_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            crypto_transaction tr;
            tr = crypto_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { valid == 0; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class crypto_performance_seq extends uvm_sequence #(crypto_transaction);
    `uvm_object_utils(crypto_performance_seq)
    
    function new(string name = "crypto_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        time start_time, end_time;
        
        start_time = $time;
        
        repeat(1000) begin
            crypto_transaction tr;
            tr = crypto_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with { valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        `uvm_info("PERF", $sformatf("Crypto Throughput Test Complete in %0t ns", end_time - start_time), UVM_LOW)
    endtask
endclass
