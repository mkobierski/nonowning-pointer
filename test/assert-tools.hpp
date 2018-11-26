
// Copyright (c) 2018, Michael Kobierski
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)

#ifndef ASSERT_TOOLS_HPP
#define ASSERT_TOOLS_HPP

#include <type_traits>
#include <utility>

/*
  ASSERT_DOESNT_COMPILE: (C++17 required due to lambda in constant expression)

    Used to check whether an expression in some context will result in a
    compilation failure.

    At least one entity in the expression must be used by passing it through the
    `dependent()' function object (it's returns its argument without
    modification), in order to make the entire expression
    instantiation-dependent.

  Usage:

    void foo(int * the_int, double number) {
      // Invalid to increment a pointer with a double
      ASSERT_DOESNT_COMPILE(the_int += dependent(number));

      // Adding an int and double is OK, so this asserts
      ASSERT_DOESNT_COMPILE(*the_int += dependent(number)); // Error.
    }

  NOTE:

    There MUST be some instantiation for which the expression is valid,
    otherwise the condition is ill-formed, no diagnostic required.  For
    example,

      void no_args() { }
      ASSERT_DOESNT_COMPILE(no_args(dependent(7))); // invalid

    is invalid since there is no possible way to call the function
    `no_args()' with an argument.


  NOTE to the implementer:

    An empty capture list should be acceptable here, since we are only
    interested in whether the function signature is valid for the expression
    in the lambda's return type, and the names in the trailing return clause
    are looked up in the scope of the lambda itself.  On GCC and Clang, this
    works as expected, however Microsoft's compiler doesn't like anything of
    the form (https://stackoverflow.com/q/53381468):

      void func() {
          int i;
          auto a = [](auto) -> decltype(i) { return int(); }
      }

    The workaround is to capture any variables required for the trailing
    return clause.  This is done with a default reference capture, and by
    placing the expression in the lambda's body as well.

  Based off of Johan Lundberg's Stack Overflow post.
  https://stackoverflow.com/a/49090642
*/
#ifdef _MSC_VER
#define ASSERT_DOESNT_COMPILE(expr)                                 \
    static_assert(!at::is_compilable(                               \
        [&](auto dependent) -> std::void_t<decltype( expr )>        \
        { expr; } )(at::detail::passthrough()),                     \
      "the expression '" #expr "' compiles but shouldn't")

#else // This is the approach that should work portably.
#define ASSERT_DOESNT_COMPILE(expr)                                 \
    static_assert(!at::is_compilable(                               \
        [](auto dependent) -> std::void_t<decltype( expr )>         \
        { } )(at::detail::passthrough()),                           \
            "the expression '" #expr "' compiles but shouldn't")
#endif

/*
  ASSERT_DELETE_DOESNT_COMPILE(expr):

    Used to test whether the expression `delete expr' will compile.

  Usage:

    void test() {
        int * a = nullptr;
        ASSERT_DELETE_DOESNT_COMPILE(a); // Error, delete possible.

        class Undeleteable {
            void operator delete(void*); // private
        };
        Undeletable * undeletable = nullptr;
        ASSERT_DELETE_DOESNT_COMPILE(undeletable); // OK, operator delete()
                                                   // inaccessible.
    }

  Output:

    error: static_assert failed due to requirement ...
           "the expression 'delete dependent(a)' compiles but shouldn't"

  When expr is "delete something", Clang and MSVC handle the object-to-pointer
  and access resolution for operator-delete in the SFINAE-enabled immediate
  context, whereas GCC doesn't.  Not sure who's right...  See:
  https://stackoverflow.com/q/53293359
*/
#if defined(__GNUG__) && !defined(__clang__) // Clang also defines __GNUG__
#ifdef ALLOW_EMPTY_DELETE_ASSERT_FOR_GCC
#define ASSERT_DELETE_DOESNT_COMPILE(expr)
#else
/*
  Explanation for the maintainer: since GCC doesn't handle delete-expressions
  in a way that lets us check their validity in a SFINAE context (see above),
  we should make sure the user knows that the statements
  ASSERT_DELETE_DOESNT_COMPILE() don't actually assert anything.

  We want this to be a (GCC specific) warning - one that is enabled by
  default.  Since GCC warns about comparisons between unrelated enum types, we
  can leverage that to give the unknowing user a diagnostic message that looks
  like this:

    In file included from main.cpp:
    main.cpp: In function ‘Status test_copy_and_move()’:
    assert-tools.hpp: warning: comparison between
      ‘enum ASSERT_DELETE_DOESNT_COMPILE_warning::the_macro_ASSERT_DELETE_DOESNT_COMPILE_doesnt_work_with_gcc’
      and ‘enum ASSERT_DELETE_DOESNT_COMPILE_solution::the_solution::is’ [-Wenum-compare]
             you_should_define -> ALLOW_EMPTY_DELETE_ASSERT_FOR_GCC < to_disable_this_warning._  \
                                                                                      ^
    main.cpp: note: in expansion of macro ‘ASSERT_DELETE_DOESNT_COMPILE’
             ASSERT_DELETE_DOESNT_COMPILE(my_var);
             ^~~~~~~~~~~~~~~~~~~~~~~~~~~~

  Once the user defines ALLOW_EMPTY_DELETE_ASSERT_FOR_GCC, the warnings will
  disappear.

  The warning is hopefully clear, however the implementation is admittedly a bit
  funky.
*/
namespace ASSERT_DELETE_DOESNT_COMPILE_warning {
  enum the_macro_ASSERT_DELETE_DOESNT_COMPILE_doesnt_work_with_gcc { };
  struct {
      the_macro_ASSERT_DELETE_DOESNT_COMPILE_doesnt_work_with_gcc
        ALLOW_EMPTY_DELETE_ASSERT_FOR_GCC;
  } dummy, *you_should_define = &dummy;
}
namespace ASSERT_DELETE_DOESNT_COMPILE_solution {
  struct the_solution { enum is { _ }; } to_disable_this_warning;
}
#define ASSERT_DELETE_DOESNT_COMPILE(expr)                              \
    {                                                                   \
        using namespace ASSERT_DELETE_DOESNT_COMPILE_warning;           \
        using namespace ASSERT_DELETE_DOESNT_COMPILE_solution;          \
        you_should_define -> ALLOW_EMPTY_DELETE_ASSERT_FOR_GCC < to_disable_this_warning._ \
            ;}
#endif
#else // Clang and MSVC handle this well.
#define ASSERT_DELETE_DOESNT_COMPILE(expr) \
    ASSERT_DOESNT_COMPILE(delete dependent(expr))
#endif

namespace at { // assert tools

namespace detail {

template< typename F, typename, typename...Args >
struct is_invokable_impl { using type = std::false_type; };

template<typename F, typename ...Args>
struct is_invokable_impl<
    F,
    // Here's the SFINAE condition:
    std::void_t<decltype(std::declval<F>()(std::declval<Args>()...))>,
    Args...>
    { using type = std::true_type; };

} // namespace detail

/*
  is_invokable: tests the boolean condition whether callable type F can be
    called with arguments of type Args....

  Usage:
    struct callable { void operator()(int, double); };
    static_assert(std::is_same_v<
      std::true_type, typename is_invokable<callable, int, double>::type>);
    static_assert(std::is_same_v<
      std::false_type, typename is_invokable<callable, nullptr_t>::type>);

    is_invokable_t<F, Args...> is provided as a type alias.

  Returns (through `type' type alias):
    true_type: f(args...) is a valid call for some F f and Args... args
    false_type: otherwise.
*/
template< typename F, typename ...Args>
struct is_invokable {
    using type = typename detail::is_invokable_impl<F, void, Args...>::type;
};

template< typename F, typename ...Args>
using is_invokable_t = typename is_invokable<F, Args...>::type;

template< typename ...Args, typename F >
auto is_invokable_f(F&&) {
    return is_invokable_t<F, Args...>();
}

/*
  compilation_tester: A class of an object that provides information on whether
    a callable type F can be called given arguments with types Args&&....

  Usage:

    int arg1, *arg2;
    auto callable = [](int, int*){ };
    decltype(compilation_tester< Callable >{ }(arg1, arg2)) a; // std::true_type
*/
template< typename F >
struct compilation_tester {
    constexpr compilation_tester() noexcept = default;
    template< typename ...Args >
    constexpr auto operator()(Args&&...) const {
        return is_invokable_t<F, Args...>{};
    }
};

template< typename F >
constexpr auto is_compilable(F&&) -> compilation_tester<F> {
    return compilation_tester<F>();
}

/*
  equality_tester: an example tester, returning a true_type for two given args
    if the expression (bool)(arg1 == arg2) is valid.

  Usage:
    constexpr auto equality_possible = at::compile_tester<at::equality_tester>();
    int a; long b;
    static_assert(
      std::is_same_v<std::true_type, decltype(equality_possible(a, b))>);
    static_assert(
      std::is_same_v<
        std::false_type, decltype(equality_possible((int*){}, (double*){}))>);

    struct A { };
    struct B : A { };
    struct C { };

    static_assert(
      std::is_same_v<
        std::true_type, decltype(equality_possible((A*){}, (B*){}))>);
    static_assert(
      std::is_same_v<
        std::false_type, decltype(equality_possible((B*){}, (C*){}))>);
*/

struct equality_tester {
    template< typename Arg1, typename Arg2 >
    auto operator()(Arg1&& arg1, Arg2&& arg2)
      -> std::void_t<decltype((bool)(arg1 == arg2))>;
};
constexpr auto equality_possible = compilation_tester<equality_tester>();

namespace detail {

// This is passed to the lambda testing the expression, so the expression can be
// instantiation-dependent even when using variables from block scope.
struct passthrough {
    template< typename Arg >
    auto operator()(Arg&& arg) -> Arg { return std::forward<Arg>(arg); }
};

} // namespace detail

} // namespace at

#endif // ASSERT_TOOLS_HPP
