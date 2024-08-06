#ifndef ROBOCALC_STATEMACHINES_STM0_H_
#define ROBOCALC_STATEMACHINES_STM0_H_

#include "RoboCalcAPI/StateMachine.h"

#ifndef ROBOCALC_THREAD_SAFE
#define THREAD_SAFE_ONLY(x)
#else
#include <mutex>
#define THREAD_SAFE_ONLY(x) x
#endif

#include "P1.h"
#include "RoboCalcAPI/Timer.h"
#include "Functions.h"
#include "DataTypes.h"
#include <assert.h>
#include <set>
#include "move2.h"
#include "move.h"

using namespace robocalc;
using namespace robocalc::functions;

template<typename ControllerType>
class stm0_StateMachine : public StateMachine<P1, ControllerType, stm0_StateMachine<ControllerType>>
{
	public:
		ControllerType& controller;
		int l;
		int a;
		const int c1;
	public:
		class S0_State_t : public robocalc::State<ControllerType>
		{
			public:
				explicit S0_State_t(ControllerType& _controller, stm0_StateMachine<ControllerType>* topLevel) 
					: robocalc::State<ControllerType>(_controller)
				{
				}
				
				S0_State_t() = delete;
			
				void enter() override
				{
					this->controller.platform->move4();
					this->controller.a1 = std::get<0>(this->controller.event1_in._args);
					this->controller.event1_in.reset();
					this->controller.a3 = std::get<0>(this->controller.event2_in._args);
					this->controller.event2_in.reset();
					this->controller.R_P1->m = (this->controller.m) + (this->controller.c1);
				}
				
				void exit() override
				{
					this->controller.platform->move1(5);
					this->controller.platform->move(1, 2);
				}
				
				void during() override
				{
					this->controller.a = ((this->controller.a3) + (this->controller.l)) + (1);
					this->controller.platform->move2(4, 5);
				}
		};
		
		class F0_State_t : public robocalc::State<ControllerType>
		{
			public:
				explicit F0_State_t(ControllerType& _controller, stm0_StateMachine<ControllerType>* topLevel) 
					: robocalc::State<ControllerType>(_controller)
				{
				}
				
				F0_State_t() = delete;
			
				void enter() override
				{
				}
				
				void exit() override
				{
				}
				
				void during() override
				{
				}
		};
		
		S0_State_t s0_State;
		F0_State_t f0_State;
		
		enum PossibleStates
		{
			s_s0,
			s_f0,
			j_i0
		} currentState = j_i0; 

	public:
		stm0_StateMachine(P1& _platform, ControllerType& _controller, stm0_StateMachine<ControllerType>* topLevel = nullptr) 
			: StateMachine<P1, ControllerType, stm0_StateMachine<ControllerType>>(_platform, _controller, topLevel), controller{_controller},
			l(0), a(0), c1(0),
			s0_State{_controller, this}, f0_State{_controller, this}
			{};
		stm0_StateMachine() = delete;
		~stm0_StateMachine() = default;
	
	
		bool canReceiveStop(std::tuple<> args)
		{
			if(blockedByStop != nullptr)
				if(blockedByStop->getSender() == this)
					return false;
												
			blockedByStop = nullptr;
		
			switch(currentState)
			{
				case s_s0:
				{
					return true;
					
					return false;
				}
				case s_f0:
				{
					
					return false;
				}
				default:
				{
					return false;
				}
			}
		}

		EventBuffer* blockedByStop = nullptr;
															
		inline void tryEmitStop(std::tuple<> args)
		{
			blockedByStop = controller.channels.tryEmitStop(this, args);
		}
		
		struct Stop_t : public EventBuffer
		{
			THREAD_SAFE_ONLY(std::mutex _mutex;)
			std::tuple<> _args;
			void* _sender = nullptr;
			void* getSender() override
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				return _sender;
			}
			
			void reset() override
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				_sender = nullptr;
			}
			
			void trigger(void* sender, std::tuple<> args)
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				_sender = sender;
			}
		} stop_in;
		
		bool canReceiveEvent2(std::tuple<int> args)
		{
			if(blockedByEvent2 != nullptr)
				if(blockedByEvent2->getSender() == this)
					return false;
												
			blockedByEvent2 = nullptr;
		
			switch(currentState)
			{
				case s_s0:
				{
					{
						const auto& a = std::get<0>(args);
						if((a3) > (4))
						{
							this->a = a;
							return true;
						}
					}
					
					return false;
				}
				case s_f0:
				{
					
					return false;
				}
				default:
				{
					return false;
				}
			}
		}

		EventBuffer* blockedByEvent2 = nullptr;
															
		inline void tryEmitEvent2(std::tuple<int> args)
		{
			blockedByEvent2 = controller.channels.tryEmitEvent2(this, args);
		}
		
		struct Event2_t : public EventBuffer
		{
			THREAD_SAFE_ONLY(std::mutex _mutex;)
			std::tuple<int> _args;
			void* _sender = nullptr;
			void* getSender() override
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				return _sender;
			}
			
			void reset() override
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				_sender = nullptr;
			}
			
			void trigger(void* sender, std::tuple<int> args)
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				_args = args;
				_sender = sender;
			}
		} event2_in;
		
	
		void execute() override
		{
			while(tryTransitions());
		
			switch(currentState)
			{
			case s_s0:
			{
				s0_State.during();
				break;
			}
			case s_f0:
			{
				f0_State.during();
				break;
			}
				default:
					break;
			}
		}
	
		bool tryTransitions() override
		{
			switch(currentState)
			{
				case s_s0:
				{
					if(stop_in.getSender() != nullptr)
					{
						s0_State.exit();
						stop_in.reset();
						f0_State.enter();
						currentState = s_f0;
						return true;	
					}
					if((this->a3) > (4))
					if(event2_in.getSender() != nullptr)
					{
						s0_State.exit();
						event2_in.reset();
						this->tryEmitTrigger1(std::tuple<int>{(this->a3) + (this->c2)});
						s0_State.enter();
						currentState = s_s0;
						return true;	
					}

					break;
				}
				case s_f0:
				{

					break;
				}
				case j_i0:
				{
					
					;
					currentState = s_s0;
					s0_State.enter();
					return true;
				}
				default:
					break;
			}
				
			return false;
		}
};
	
#endif
