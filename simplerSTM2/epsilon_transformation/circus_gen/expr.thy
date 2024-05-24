theory 	imports Axiomatic_Circus
begin



	
chantype internal_chan_stm0 = 
	internal__NID_i0 :: unit 	
	internal__NID_s0 :: unit 	
	internal__NID_f0 :: unit 	
	
chantype flowchan_stm0 = 
	interrupt :: unit 	
	exited :: unit 	
	exit :: unit 	
	terminate :: unit 	
	
chantype variable_chan_stm0 = 
	get_a :: int	
	set_a :: int	
	setL_a :: int	
	setR_a :: int	
	
chantype event_chan_stm0 = 
	stop_in :: unit 	
	stop_out :: unit 	
	stop__NID_i0_in :: unit 	
	stop__NID_i0_out :: unit 	
	stop__NID_s0_in :: unit 	
	stop__NID_s0_out :: unit 	
	stop__NID_f0_in :: unit 	
	stop__NID_f0_out :: unit 	
	trigger1_in :: unit 	
	trigger1_out :: unit 	
	trigger1__NID_i0_in :: unit 	
	trigger1__NID_i0_out :: unit 	
	trigger1__NID_s0_in :: unit 	
	trigger1__NID_s0_out :: unit 	
	trigger1__NID_f0_in :: unit 	
	trigger1__NID_f0_out :: unit 	
	event1_in :: unit 	
	event1_out :: unit 	
	event1__NID_i0_in :: unit 	
	event1__NID_i0_out :: unit 	
	event1__NID_s0_in :: unit 	
	event1__NID_s0_out :: unit 	
	event1__NID_f0_in :: unit 	
	event1__NID_f0_out :: unit 	
	
chantype junc_chan_i0 = 
	enter_i0 :: unit 	
	interrupt_i0 :: unit 	
	
chantype st_chan_s0 = 
	enter_s0 :: unit 	
	entered_s0 :: unit 	
	interrupt_s0 :: unit 	
	enteredL_s0 :: unit 	
	enteredR_s0 :: unit 	
	
chantype st_chan_f0 = 
	enter_f0 :: unit 	
	entered_f0 :: unit 	
	interrupt_f0 :: unit 	
	enteredL_f0 :: unit 	
	enteredR_f0 :: unit 	

 

end


