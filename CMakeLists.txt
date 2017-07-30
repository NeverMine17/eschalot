cmake_minimum_required(VERSION 3.2)
project(eschalot-cxx CXX)

set(CMAKE_CXX_STANDARD 11)

add_definitions(-O3)

link_libraries(ssl pthread crypto)

add_executable(eschalot eschalot.cpp)
add_executable(typecard typecard.cpp)
add_executable(worgen worgen.cpp)