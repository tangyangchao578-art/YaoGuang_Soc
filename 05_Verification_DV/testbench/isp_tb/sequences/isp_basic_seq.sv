class isp_basic_seq extends uvm_sequence #(isp_transaction);
    `uvm_object_utils(isp_basic_seq)
    
    function new(string name = "isp_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(100) begin
            isp_transaction tr;
            tr = isp_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { pixel_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class isp_demosaic_seq extends uvm_sequence #(isp_transaction);
    `uvm_object_utils(isp_demosaic_seq)
    
    function new(string name = "isp_demosaic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 1000; i++) begin
            isp_transaction tr;
            tr = isp_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { pixel_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class isp_awb_seq extends uvm_sequence #(isp_transaction);
    `uvm_object_utils(isp_awb_seq)
    
    function new(string name = "isp_awb_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 100; i++) begin
            isp_transaction tr;
            tr = isp_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { pixel_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass
