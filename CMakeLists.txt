
# Copyright (c) 2018, Michael Kobierski
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE.txt or copy at
# https://www.boost.org/LICENSE_1_0.txt)

cmake_minimum_required(VERSION 3.1)

project(nonowningptr VERSION 1.0.0)
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

set(nonowningptr_headers
  ${PROJECT_SOURCE_DIR}/include/nonowningptr.hpp
  ${PROJECT_SOURCE_DIR}/include/nonowningptr-detail.hpp)

add_library(nonowningptr INTERFACE)
target_sources(nonowningptr INTERFACE ${nonowningptr_headers})

target_include_directories(nonowningptr INTERFACE
    $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# So Visual Studio has a project for the header-only library.
# See https://gitlab.kitware.com/cmake/cmake/issues/15234
add_custom_target(nonowningptr-ide SOURCES ${nonowningptr_headers})

add_subdirectory(test)

install(FILES ${nonowningptr_headers} DESTINATION include)
