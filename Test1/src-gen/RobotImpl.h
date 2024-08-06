#ifndef __ROBOT_IMPL_H__
#define __ROBOT_IMPL_H__

#include "P1.h"

#include <set>
#include <algorithm>
#include <iostream>

class RobotImpl : public P1
{
public:
	
	void move2(double lv, int a) override
	{
		std::cout<<"Operation move2 invoked on robot platform"<<std::endl;
	}
	void move4() override
	{
		std::cout<<"Operation move4 invoked on robot platform"<<std::endl;
	}
	void move1(int m) override
	{
		std::cout<<"Operation move1 invoked on robot platform"<<std::endl;
	}
	void move5(double lv, int a) override
	{
		std::cout<<"Operation move5 invoked on robot platform"<<std::endl;
	}
};

#endif
