class isp_performance_seq extends uvm_sequence #(isp_transaction);
    `uvm_object_utils(isp_performance_seq)
    
    int num_pixels = 1000000;
    
    function new(string name = "isp_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        isp_transaction tr;
        time start_time, end_time;
        
        start_time = $time;
        
        repeat(num_pixels) begin
            tr = isp_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with { pixel_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        `uvm_info("PERF", $sformatf("ISP Processing: %0d pixels in %0t ns", num_pixels, end_time - start_time), UVM_LOW)
    endtask
endclass
