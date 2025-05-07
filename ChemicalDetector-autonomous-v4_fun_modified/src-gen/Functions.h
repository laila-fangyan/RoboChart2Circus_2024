
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
		bool isInjection( f);
		bool isBijection( f);
		bool isFinite(std::set<> s);
		 second(std::tuple<, > p);
		 intensity(std::vector<GasSensor> gs);
		 tr_closure( r);
		bool isFiniteInjection( f);
		 funcomp( s,  r);
		bool isTotalSurjection( f);
		Angle location(std::vector<GasSensor> gs);
		std::tuple<, > maplet( x,  y);
		 id();
		 rres( r, std::set<> b);
		std::set<> rimage( r, std::set<> a);
		 rinv( r);
		 override( r,  s);
		 dres(std::set<> a,  r);
		bool isSurjection( f);
		bool partitions( f, std::set<> a);
		std::set<> inter(std::set<> s1, std::set<> s2);
		 relcomp( r,  s);
		std::set<> ran( r);
		std::set<> union(std::set<> s1, std::set<> s2);
		 refl_tr_closure( r);
		bool isTotalInjection( f);
		std::set<> dom( r);
		bool notin( m, std::set<> s);
		std::set<> Union(std::set<std::set<>> A);
		 rsub( r, std::set<> b);
		 dsub(std::set<> a,  r);
		Status analysis(std::vector<GasSensor> gs);
		bool subset(std::set<> ss, std::set<> s);
		bool isFiniteFunction( f);
		bool isTotal( f);
		Angle angle(unsigned int x);
		bool disjoint( f);
		std::set<> Inter(std::set<std::set<>> A);
		std::set<> symetric_diff(std::set<> s1, std::set<> s2);
		std::set<> diff(std::set<> s1, std::set<> s2);
		unsigned int card(std::set<> A);
		bool subseteq(std::set<> ss, std::set<> s);
		 first(std::tuple<, > p);
		
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
