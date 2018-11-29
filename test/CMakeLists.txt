
# Copyright (c) 2018, Michael Kobierski
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE.txt or copy at
# https://www.boost.org/LICENSE_1_0.txt)

add_executable(test-nonowning11 main11.cpp)
target_link_libraries(test-nonowning11 nonowning_ptr)
add_test(NAME test-nonowning11-test COMMAND test-nonowning11)

set(CMAKE_CXX_STANDARD 17)

add_executable(test-nonowning main.cpp)
target_link_libraries(test-nonowning nonowning_ptr)
add_test(NAME test-nonowning-test COMMAND test-nonowning)



