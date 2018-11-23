
// Copyright (c) 2018, Michael Kobierski
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)

#ifndef STATUS_HPP
#define STATUS_HPP

#include <exception>

class Status {
public:
    struct NotOkException : std::exception { };
    enum class Option { fail = -1, ok = 0 };

    Status(Option code) noexcept : code_(code) { }

    Option code() const noexcept { return code_; }

    static Status ok() noexcept { return Option::ok; }
    static Status fail() noexcept { return Option::fail; }

private:
    Option code_;
};

void check(Status const & status) {
    if(status.code() != Status::Option::ok) {
        throw Status::NotOkException();
    }
}

#endif // STATUS_HPP
