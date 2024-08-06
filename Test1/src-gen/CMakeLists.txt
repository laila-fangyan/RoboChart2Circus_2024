cmake_minimum_required (VERSION 2.8)
project (RoboCalc_Autogen)

add_executable(MainExe main.cpp C1.h P1.h)
add_executable(MainExeInteractive main.cpp C1.h P1.h)
target_compile_definitions(MainExeInteractive PUBLIC -DROBOCALC_INTERACTIVE)

include(CMakeCustom.cmake OPTIONAL)
