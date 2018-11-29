
# Copyright (c) 2018, Michael Kobierski
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE.txt or copy at
# https://www.boost.org/LICENSE_1_0.txt)

add_executable(test-nonowningptr11 main11.cpp)
target_link_libraries(test-nonowningptr11 nonowningptr)
add_test(NAME test-nonowningptr11-test COMMAND test-nonowningptr11)

set(CMAKE_CXX_STANDARD 17)

add_executable(test-nonowningptr main.cpp)
target_link_libraries(test-nonowningptr nonowningptr)
add_test(NAME test-nonowningptr-test COMMAND test-nonowningptr)



