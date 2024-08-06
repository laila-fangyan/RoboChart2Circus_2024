#ifndef ROBOCALC_API_STATE_H_
#define ROBOCALC_API_STATE_H_

#include <string>

namespace robocalc
{
	class EventBuffer
	{
	public:
		virtual void* getSender() = 0;
		virtual void reset() = 0;
	};
	
	template<class StateMachineType>
	class State;
	
	template<typename RobotType, typename ControllerType, typename TopLevelStateMachineType>
	class StateMachine
	{
	public:
		StateMachine(RobotType& _robot, ControllerType& _controller, TopLevelStateMachineType* topLevel): robot(_robot), controller(_controller) {}
		StateMachine() = delete;
		
		virtual bool tryTransitions() = 0;
		virtual void execute() = 0;
		RobotType& robot;
		ControllerType& controller;
	};
	
	template<class ControllerType>
	class State
	{
	public:
		ControllerType& controller;
			
		State(ControllerType& _controller) : controller(_controller) {}
		State() = delete;
		virtual void enter() = 0;
		virtual void exit() = 0;
		virtual void during() = 0;
	};
				
	template<class ControllerType>
	class InitialState : public State<ControllerType>
	{
	public:
		InitialState() {}
		virtual void enter() {};
		virtual void exit() {};
		virtual void during() {};
	};
	
	template<typename StateMachineType, typename RobotType, typename ControllerType, typename TopLevelStateMachineType>
	class CompositeState : public State<ControllerType>
	{
	public:
		CompositeState(RobotType& robot, ControllerType& controller, TopLevelStateMachineType* topLevel) 
			: State<ControllerType>{controller}, sm{robot, controller, topLevel} {}
			
		CompositeState() = delete;
		
		virtual void enter() 
		{
		}
		
		virtual void during() 
		{
			while(sm.tryTransitions());
			sm.execute();
		}
		
		virtual void exit() 
		{
		}
		
		StateMachineType sm;
	};
}

#endif

