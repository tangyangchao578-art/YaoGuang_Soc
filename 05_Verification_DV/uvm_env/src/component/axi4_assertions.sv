`ifndef AXI4_ASSERTIONS_SVH
`define AXI4_ASSERTIONS_SVH

module axi4_assertions (
  input clk,
  input rst_n,
  axi4_if.tb vif
);

  property awvalid_wait;
    @(posedge clk) disable iff (!rst_n)
    (vif.awvalid && !vif.awready) |=> (vif.awvalid && !vif.awready) until (vif.awready);
  endproperty

  property arvalid_wait;
    @(posedge clk) disable iff (!rst_n)
    (vif.arvalid && !vif.arready) |=> (vif.arvalid && !vif.arready) until (vif.arready);
  endproperty

  property wvalid_wait;
    @(posedge clk) disable iff (!rst_n)
    (vif.wvalid && !vif.wready) |=> (vif.wvalid && !vif.wready) until (vif.wready);
  endproperty

  property bvalid_wait;
    @(posedge clk) disable iff (!rst_n)
    (vif.bvalid && !vif.bready) |=> (vif.bvalid && !vif.bready) until (vif.bready);
  endproperty

  property rvalid_wait;
    @(posedge clk) disable iff (!rst_n)
    (vif.rvalid && !vif.rready) |=> (vif.rvalid && !vif.rready) until (vif.rready);
  endproperty

  property wlast_check;
    @(posedge clk) disable iff (!rst_n)
    (vif.wvalid && !vif.wlast) |=> !vif.wlast until (vif.wlast);
  endproperty

  property rlast_check;
    @(posedge clk) disable iff (!rst_n)
    (vif.rvalid && !vif.rlast) |=> !vif.rlast until (vif.rlast);
  endproperty

  awvalid_wait_assert: assert property (awvalid_wait) else `DV_ERROR("AWVALID wait timeout");
  arvalid_wait_assert: assert property (arvalid_wait) else `DV_ERROR("ARVALID wait timeout");
  wvalid_wait_assert: assert property (wvalid_wait) else `DV_ERROR("WVALID wait timeout");
  bvalid_wait_assert: assert property (bvalid_wait) else `DV_ERROR("BVALID wait timeout");
  rvalid_wait_assert: assert property (rvalid_wait) else `DV_ERROR("RVALID wait timeout");
  wlast_check_assert: assert property (wlast_check) else `DV_ERROR("WLAST timing error");
  rlast_check_assert: assert property (rlast_check) else `DV_ERROR("RLAST timing error");

endmodule

`endif
