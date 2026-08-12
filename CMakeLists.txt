cmake_minimum_required(VERSION 3.10)
project(problem_015 CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(code main.cpp)
target_compile_options(code PRIVATE -O2 -Wall)

# Static binary: sandbox-friendly (no shared library dependencies at runtime)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static")
