
# Copyright (c) 2018, Michael Kobierski
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE.txt or copy at
# https://www.boost.org/LICENSE_1_0.txt)

cmake_minimum_required(VERSION 3.1)

project(nonowning_ptr VERSION 1.0.0)
enable_testing()

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_EXTENSIONS OFF)

# compiler flags - increase warnings, set optimizations off
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU"
    OR CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -O0 -g")
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /W4 /WX /EHsc /Od /ZI")
endif()

set(nonowning_headers 
  ${PROJECT_SOURCE_DIR}/include/nonowning.hpp
  ${PROJECT_SOURCE_DIR}/include/nonowning-detail.hpp)

set(HEADERS include/nonowning.hpp include/nonowning-detail.hpp)
add_library(nonowning_ptr INTERFACE)
target_sources(nonowning_ptr INTERFACE ${nonowning_headers})

target_include_directories(nonowning_ptr INTERFACE
    $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# So Visual Studio has a project for the header-only library.
# See https://gitlab.kitware.com/cmake/cmake/issues/15234
add_custom_target(nonowning_ptr-ide SOURCES ${nonowning_headers})

add_subdirectory(test)

install(FILES ${nonowning_headers} DESTINATION include)
