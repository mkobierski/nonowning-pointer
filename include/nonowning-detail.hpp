
// Copyright (c) 2018, Michael Kobierski
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)

#ifndef NONOWNING_DETAIL_HPP
#define NONOWNING_DETAIL_HPP

// Make sure mixed-mode calls make the right conversions.  Without this, the
// compiler will try to do a comparison through implicit conversion to void *.
// Also, these will produce a compilation error if the comparison between raw
// pointer types wouldn't be valid, citing "comparison between distinct pointer
// types lacks a cast".
#define COMPARABLE_HELPER_MEMBER(name, oper)                            \
    template< typename Type1, typename Type2 >                          \
    static bool name(Type1* lhs, Type2* rhs,                            \
      decltype((Type1*)nullptr oper (Type2*)nullptr)) {                 \
        return lhs oper rhs;                                            \
    }                                                                   \
    template< typename Type1, typename Type2 > /* not defined */        \
    static not_comparable name(Type1*, Type2*, bool_type)
    ;

namespace nown_detail {

class comparable_helper {
    struct not_comparable { };
    struct bool_type { bool_type(bool) { }; };

public:
    COMPARABLE_HELPER_MEMBER(eq, ==);
    COMPARABLE_HELPER_MEMBER(ne, !=);
    COMPARABLE_HELPER_MEMBER(lt, <);
    COMPARABLE_HELPER_MEMBER(gt, >);
    COMPARABLE_HELPER_MEMBER(le, <=);
    COMPARABLE_HELPER_MEMBER(ge, >=);
};

} // namespace nown_detail

#undef COMPARABLE_HELPER_MEMBER


#endif // NONOWNING_DETAIL_HPP
