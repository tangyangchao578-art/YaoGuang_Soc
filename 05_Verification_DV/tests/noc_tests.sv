class noc_routing_test extends dv_base_test;

  `uvm_component_utils(noc_routing_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing NoC routing")

    // Test destination routing
    for (int i = 0; i < 16; i++) begin
      noc_routing_seq seq = noc_routing_seq::type_id::create("noc_route_seq");
      seq.destination = i;
      seq.start(env.agent.sequencer);
    end

    // Test broadcast routing
    begin
      noc_broadcast_seq seq = noc_broadcast_seq::type_id::create("noc_bcast_seq");
      seq.start(env.agent.sequencer);
    end

    phase.drop_objection(this);
  endtask

endclass

class noc_qos_test extends dv_base_test;

  `uvm_component_utils(noc_qos_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing NoC QoS")

    // Test priority arbitration
    for (int priority = 0; priority < 4; priority++) begin
      noc_qos_seq seq = noc_qos_seq::type_id::create("noc_qos_seq");
      seq.priority = priority;
      seq.start(env.agent.sequencer);
    end

    // Test traffic shaping
    begin
      noc_shaping_seq seq = noc_shaping_seq::type_id::create("noc_shape_seq");
      seq.start(env.agent.sequencer);
    end

    phase.drop_objection(this);
  endtask

endclass

class noc_congestion_test extends dv_base_test;

  `uvm_component_utils(noc_congestion_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing NoC congestion control")

    // Inject high traffic and verify no deadlock
    fork
      begin
        for (int i = 0; i < 10; i++) begin
          noc_traffic_seq seq = noc_traffic_seq::type_id::create("noc_traffic_seq");
          seq.priority = i % 4;
          seq.start(env.agent.sequencer);
        end
      end
    join_none

    #10000;

    phase.drop_objection(this);
  endtask

endclass

class noc_performance_test extends dv_base_test;

  `uvm_component_utils(noc_performance_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing NoC performance")

    // Measure bandwidth
    real bandwidth;
    bandwidth = measure_bandwidth();

    `DV_INFO($sformatf("Measured bandwidth: %0f GB/s", bandwidth))

    // Verify bandwidth requirement
    `DV_CHECK(bandwidth >= 2.0, "Bandwidth requirement not met")

    phase.drop_objection(this);
  endtask

  virtual function real measure_bandwidth();
    integer bytes_transferred = 0;
    real start_time, end_time;

    start_time = $realtime;

    for (int i = 0; i < 1000; i++) begin
      noc_bandwidth_seq seq = noc_bandwidth_seq::type_id::create("noc_bw_seq");
      seq.start(env.agent.sequencer);
      bytes_transferred += 64 * 16; // 16 beats of 64 bytes
    end

    end_time = $realtime;
    return bytes_transferred / (end_time - start_time) / 1e9;
  endfunction

endclass
