class isp_error_seq extends uvm_sequence #(isp_transaction);
    `uvm_object_utils(isp_error_seq)
    
    function new(string name = "isp_error_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            isp_transaction tr;
            tr = isp_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { pixel_valid == 0; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass
