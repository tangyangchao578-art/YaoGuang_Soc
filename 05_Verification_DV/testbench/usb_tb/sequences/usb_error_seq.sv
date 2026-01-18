class usb_error_seq extends uvm_sequence #(usb_transaction);
    `uvm_object_utils(usb_error_seq)
    
    function new(string name = "usb_error_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            usb_transaction tr;
            tr = usb_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 0; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class usb_crc_err_seq extends uvm_sequence #(usb_transaction);
    `uvm_object_utils(usb_crc_err_seq)
    
    function new(string name = "usb_crc_err_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            usb_transaction tr;
            tr = usb_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; tx_data[7:0] == 8'h00; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass
