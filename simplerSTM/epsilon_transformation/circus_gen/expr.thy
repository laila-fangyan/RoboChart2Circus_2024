theory 	imports Axiomatic_Circus
begin



	
chantype internal_chan_stm0 = 
	internal__NID_i0 :: unit 	
	internal__NID_s0 :: unit 	
	internal__NID_s1 :: unit 	
	internal__NID_s2 :: unit 	
	internal__NID_f0 :: unit 	
	internal__NID_s3 :: unit 	
	internal__NID_s4 :: unit 	
	internal__NID_j0 :: unit 	
	
chantype flowchan_stm0 = 
	interrupt :: unit 	
	exited :: unit 	
	exit :: unit 	
	terminate :: unit 	
	
chantype variable_chan_stm0 = 
	get_input :: int	
	set_input :: int	
	setL_input :: int	
	setR_input :: int	
	
chantype event_chan_stm0 = 
	stop_in :: unit 	
	stop_out :: unit 	
	stop__NID_i0_in :: unit 	
	stop__NID_i0_out :: unit 	
	stop__NID_s0_in :: unit 	
	stop__NID_s0_out :: unit 	
	stop__NID_s1_in :: unit 	
	stop__NID_s1_out :: unit 	
	stop__NID_s2_in :: unit 	
	stop__NID_s2_out :: unit 	
	stop__NID_f0_in :: unit 	
	stop__NID_f0_out :: unit 	
	stop__NID_s3_in :: unit 	
	stop__NID_s3_out :: unit 	
	stop__NID_s4_in :: unit 	
	stop__NID_s4_out :: unit 	
	stop__NID_j0_in :: unit 	
	stop__NID_j0_out :: unit 	
	status_in :: unit 	
	status_out :: unit 	
	status__NID_i0_in :: unit 	
	status__NID_i0_out :: unit 	
	status__NID_s0_in :: unit 	
	status__NID_s0_out :: unit 	
	status__NID_s1_in :: unit 	
	status__NID_s1_out :: unit 	
	status__NID_s2_in :: unit 	
	status__NID_s2_out :: unit 	
	status__NID_f0_in :: unit 	
	status__NID_f0_out :: unit 	
	status__NID_s3_in :: unit 	
	status__NID_s3_out :: unit 	
	status__NID_s4_in :: unit 	
	status__NID_s4_out :: unit 	
	status__NID_j0_in :: unit 	
	status__NID_j0_out :: unit 	
	trigger1_in :: unit 	
	trigger1_out :: unit 	
	trigger1__NID_i0_in :: unit 	
	trigger1__NID_i0_out :: unit 	
	trigger1__NID_s0_in :: unit 	
	trigger1__NID_s0_out :: unit 	
	trigger1__NID_s1_in :: unit 	
	trigger1__NID_s1_out :: unit 	
	trigger1__NID_s2_in :: unit 	
	trigger1__NID_s2_out :: unit 	
	trigger1__NID_f0_in :: unit 	
	trigger1__NID_f0_out :: unit 	
	trigger1__NID_s3_in :: unit 	
	trigger1__NID_s3_out :: unit 	
	trigger1__NID_s4_in :: unit 	
	trigger1__NID_s4_out :: unit 	
	trigger1__NID_j0_in :: unit 	
	trigger1__NID_j0_out :: unit 	
	trigger2_in :: unit 	
	trigger2_out :: unit 	
	trigger2__NID_i0_in :: unit 	
	trigger2__NID_i0_out :: unit 	
	trigger2__NID_s0_in :: unit 	
	trigger2__NID_s0_out :: unit 	
	trigger2__NID_s1_in :: unit 	
	trigger2__NID_s1_out :: unit 	
	trigger2__NID_s2_in :: unit 	
	trigger2__NID_s2_out :: unit 	
	trigger2__NID_f0_in :: unit 	
	trigger2__NID_f0_out :: unit 	
	trigger2__NID_s3_in :: unit 	
	trigger2__NID_s3_out :: unit 	
	trigger2__NID_s4_in :: unit 	
	trigger2__NID_s4_out :: unit 	
	trigger2__NID_j0_in :: unit 	
	trigger2__NID_j0_out :: unit 	
	trigger3_in :: unit 	
	trigger3_out :: unit 	
	trigger3__NID_i0_in :: unit 	
	trigger3__NID_i0_out :: unit 	
	trigger3__NID_s0_in :: unit 	
	trigger3__NID_s0_out :: unit 	
	trigger3__NID_s1_in :: unit 	
	trigger3__NID_s1_out :: unit 	
	trigger3__NID_s2_in :: unit 	
	trigger3__NID_s2_out :: unit 	
	trigger3__NID_f0_in :: unit 	
	trigger3__NID_f0_out :: unit 	
	trigger3__NID_s3_in :: unit 	
	trigger3__NID_s3_out :: unit 	
	trigger3__NID_s4_in :: unit 	
	trigger3__NID_s4_out :: unit 	
	trigger3__NID_j0_in :: unit 	
	trigger3__NID_j0_out :: unit 	
	
chantype junc_chan_i0 = 
	enter_i0 :: unit 	
	interrupt_i0 :: unit 	
	
chantype st_chan_s0 = 
	enter_s0 :: unit 	
	entered_s0 :: unit 	
	interrupt_s0 :: unit 	
	enteredL_s0 :: unit 	
	enteredR_s0 :: unit 	
	
chantype st_chan_s1 = 
	enter_s1 :: unit 	
	entered_s1 :: unit 	
	interrupt_s1 :: unit 	
	enteredL_s1 :: unit 	
	enteredR_s1 :: unit 	
	
chantype st_chan_s2 = 
	enter_s2 :: unit 	
	entered_s2 :: unit 	
	interrupt_s2 :: unit 	
	enteredL_s2 :: unit 	
	enteredR_s2 :: unit 	
	
chantype st_chan_f0 = 
	enter_f0 :: unit 	
	entered_f0 :: unit 	
	interrupt_f0 :: unit 	
	enteredL_f0 :: unit 	
	enteredR_f0 :: unit 	
	
chantype st_chan_s3 = 
	enter_s3 :: unit 	
	entered_s3 :: unit 	
	interrupt_s3 :: unit 	
	enteredL_s3 :: unit 	
	enteredR_s3 :: unit 	
	
chantype st_chan_s4 = 
	enter_s4 :: unit 	
	entered_s4 :: unit 	
	interrupt_s4 :: unit 	
	enteredL_s4 :: unit 	
	enteredR_s4 :: unit 	
	
chantype junc_chan_j0 = 
	enter_j0 :: unit 	
	interrupt_j0 :: unit 	

 

end


