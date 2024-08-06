#include <iostream>
#include <unistd.h>
#include "RobotImpl.h"
#include "C1.h"

RobotImpl robot;

static constexpr long cycleDuration = 100e3;
			
int main(int argc, char** argv)
{
	C1 c1{robot};
	
	while(true)
	{
		robot.Sense();
		
		// Signals to robot platform
		
		// Signals from robot platform
		// Signals between controllers
				
		c1.Execute();
		
		robot.Actuate();
		
		#ifdef ROBOCALC_INTERACTIVE
		
		std::cout<<"Looped. Press enter for next iteration or q to quit."<<std::endl;
		char c;
		bool processingInput = true;
		while(processingInput)
		{
			std::cin.get(c);
			switch(c)
			{
				case '\n':
				{
					processingInput = false;
					break;
				}
				case 'q':
				case 'Q':
				{
					std::cout<<"Exiting"<<std::endl;
					return 0;
					break;
				}
				default:
					break;
			}
		}
		
		#else
			usleep(cycleDuration);				
		#endif
	}
	
	return 0;
}
