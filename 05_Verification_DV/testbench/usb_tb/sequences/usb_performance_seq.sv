class usb_performance_seq extends uvm_sequence #(usb_transaction);
    `uvm_object_utils(usb_performance_seq)
    
    int num_transactions = 10000;
    real throughput;
    time start_time, end_time;
    
    function new(string name = "usb_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        usb_transaction tr;
        
        start_time = $time;
        
        repeat(num_transactions) begin
            tr = usb_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        throughput = (num_transactions * 8) / (end_time - start_time);
        
        `uvm_info("PERF", $sformatf("USB Throughput: %0.2f Gbps", throughput / 1e9), UVM_LOW)
    endtask
endclass
