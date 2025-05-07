
#ifndef ROBOCALC_FUNCTIONS_H_
#define ROBOCALC_FUNCTIONS_H_

#include "DataTypes.h"
#include <vector>
#include <set>

namespace robocalc
{
	namespace functions
	{
		bool goreq(null i1, null i2);
		 intensity(std::vector<GasSensor> gs);
		Status analysis(std::vector<GasSensor> gs);
		Angle location(std::vector<GasSensor> gs);
		unsigned int card(std::set<> A);
		unsigned int angle(unsigned int x);
		Angle angle(unsigned int x);
		
		template<typename T>
		std::set<T> set_union(std::set<T> s1, std::set<T> s2)
		{
			std::set<T> ret;
			ret.insert(s1.begin(), s1.end());
			ret.insert(s2.begin(), s2.end());
			return ret;
		}
		
		template<typename T>
		unsigned int size(std::set<T> s)
		{
			return s.size();
		}
	}
}

#endif
