#ifndef ROBOCALC_ROBOT_P1_H_
#define ROBOCALC_ROBOT_P1_H_

#include "DataTypes.h"

class P1 {
public:
	P1() = default; 
	virtual ~P1() = default;
	virtual void Sense() {};
	virtual void Actuate() {};
	int pv1;
	
	virtual void move2(double lv, int a) = 0;
	virtual void move4() = 0;
	virtual void move1(int m) = 0;
	virtual void move5(double lv, int a) = 0;
};

#endif
