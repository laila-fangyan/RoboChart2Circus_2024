#ifndef ROBOCALC_CONTROLLERS_C1_H_
#define ROBOCALC_CONTROLLERS_C1_H_

#include "P1.h"
#include "RoboCalcAPI/Controller.h"
#include "DataTypes.h"

#include "stm0.h"
#include "stm0.h"

class C1: public robocalc::Controller 
{
public:
	C1(P1& _platform) : platform(&_platform){};
	C1() : platform(nullptr){};
	
	~C1() = default;
	
	void Execute()
	{
		stm0.execute();
		stm0.execute();
	}
	
	struct Channels
	{
		C1& instance;
		Channels(C1& _instance) : instance(_instance) {}
		
	};
	
	Channels channels{*this};
	
	P1* platform;
	stm0_StateMachine<C1> stm0{*platform, *this, &stm0};
	stm0_StateMachine<C1> stm0{*platform, *this, &stm0};
};

#endif
