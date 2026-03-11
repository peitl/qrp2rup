cmake_minimum_required(VERSION 3.10)
project(qrp2rup)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall")
if (STATIC)
	message(STATUS "static build")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static -static-libgcc -static-libstdc++")
endif ()

add_subdirectory(src)
