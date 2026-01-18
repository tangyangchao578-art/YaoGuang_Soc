class usb_basic_seq extends uvm_sequence #(usb_transaction);
    `uvm_object_utils(usb_basic_seq)
    
    int num_transactions = 100;
    
    function new(string name = "usb_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(num_transactions) begin
            usb_transaction tr;
            tr = usb_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class usb_bulk_seq extends uvm_sequence #(usb_transaction);
    `uvm_object_utils(usb_bulk_seq)
    
    int packet_size = 512;
    
    function new(string name = "usb_bulk_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < packet_size; i++) begin
            usb_transaction tr;
            tr = usb_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class usb_control_seq extends uvm_sequence #(usb_transaction);
    `uvm_object_utils(usb_control_seq)
    
    function new(string name = "usb_control_seq");
        super.new(name);
    endtask
    
    virtual task body();
        usb_transaction tr;
        
        for(int i = 0; i < 8; i++) begin
            tr = usb_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with { tx_valid == 1; }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass
