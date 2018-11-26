
// Copyright (c) 2018, Michael Kobierski
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)

#ifndef NONOWNING_HPP
#define NONOWNING_HPP

#include "nonowning-detail.hpp"

#include <cstddef> // nullptr_t, ptrdiff_t
#include <type_traits>
#include <utility>
#include <iterator>

namespace nown { // nonowning

template< typename Type >
class NonOwningPtr {
    class delete_ambiguifier;

    enum { is_const = std::is_const<Type>::value };
    using void_type = typename std::conditional<is_const, const void, void
        >::type;

public:
    using PointeeType = Type;

    /*
      Constructors:

      We should support the implicit conversion of a bare pointer to a
      NonOwningPtr pointer, therefore the single-parameter constructor is not
      explicit.  By default, a constructed NonOwningPtr is equal to nullptr.

      It should also be possible to construct a given NonOwningPtr from a
      NonOwningPtr for another type given that the underlying source pointer can
      be converted to the destination's underlying pointer.  A templated
      constructor provides this functionality.

      Note that copying and moving should amount to the same thing (same
      performance), as the NonOwningPtr class only holds a single member: a
      pointer.  This means we don't have to explicitly declare and default the
      copy/move constructors and assignment operators to protect against future
      addition of a destructor (for example if we want to log destructions) that
      might inadvertently disable the move ops.  Even if this happens, the
      performace should remain unchanged.
    */
    constexpr NonOwningPtr(Type * ptr = nullptr) noexcept : ptr_(ptr) { }

    template<typename OtherType,
        typename = typename std::
            enable_if<std::is_convertible<OtherType *, Type *>::value>::type>
    constexpr NonOwningPtr(NonOwningPtr<OtherType> const & other) noexcept
      : ptr_(other.get()) { }

    /*
      A typical use case for a pointer is checking whether it is null or not.
      We want to support this use case, so provide an explicit conversion to
      bool.
    */
    constexpr explicit operator bool() const noexcept { return ptr_; }

    /*
      Given a function like `void foo(int *) { }' and a `NonOwningPtr<int> ptr',
      we want to support calls like `foo(ptr)'.  This is achievable by providing
      an implicit conversion to the underlying pointer type.

      Note that this also makes the delete-expression `delete ptr' valid, since
      the first step of a delete-expression is to implicitly convert the operand
      (in this case a NonOwningPtr) to a pointer-to-object.  These are prevented
      by ambiguating the implicit conversion (see below).
    */
    constexpr operator Type * () const noexcept { return ptr_; }

    /*
      The entire motivation of the NonOwningPtr class is to prevent a user from
      deleting a resource explicitly owned by somebody else.  As noted above,
      implicit conversion to the underlying pointer type makes the expression
      `delete ptr' valid, so the goal here is to make in ill formed due to
      ambiguation.  If the compiler can't figure out how to conver a class type
      to a pointer-to-object, how can the object be deleted?

      To ambiguate, we provide an (undefined) implicit conversion to a pointer
      to private and undefined type `delete_ambiguifier'.  The
      `delete_ambiguifier' is qualified with const and volatile.  To show that
      this is required, consider the following case if it weren't.

          void foo() {
              NonOwningPtr<int const> pci; // pointer to const int
              void * v = pci; // discards const qualifier
          }

      The class NonOwningPtr<int const> has a conversion operator to int const*,
      but further converting that to a void * discards the const qualifier and
      is therefore disallowed.  However, since we are providing a conversion
      from NonOwningPtr<int const> to pointer to (hypothetically) non-const
      `delete_ambiguifier', that following conversion sequence works:

          NonOwningPtr<int const> -> delete_ambiguifier * -> void *

      To prevent this at link time, the conversion to delete_ambiguifier is left
      undefined.  By making it at least a cv-qualified as the NonOwningPtr's
      pointee-type, though, the conversion will also be disallowed at compile
      time.  We don't lose the desired effect of ambiguifying delete
      expressions, since in that case const and volatile qualifiers are ignored.
    */
    constexpr operator delete_ambiguifier const volatile * () const noexcept;

    /*
      Should be able to convert to cv-void*, however `delete_ambiguifier' also
      ambiguifies this case.
      TODO: explain better.
    */
    constexpr operator void_type * () const noexcept { return ptr_; }

    /*
      Normal smart pointer interface, and easy access to underlying pointer.
    */
    constexpr Type * operator->() const noexcept { return ptr_; }
    constexpr Type & operator*() const noexcept { return *ptr_; }
    constexpr Type * get() const noexcept { return ptr_; }

#ifdef _MSC_VER
    /*
      Implementations of operator->*().

      These shouldn't be required because e1->*e2 should be equivalent to
      the expression (*e1).*e2, and we already provide operator*().  However,
      unless we provide these, MSVC will not compile expressions involving ->*.

      There are three (ignoring volatile) to overload:
          pointer-to-member: T Type::*
          pointer-to-member-function: T (Type::*)(Args...)
          pointer-to-const-member-function: T (Type::*)(Args...) const

      The member-function ones must be usable like this:

          class A { void foo(); }
          NonOwningPtr<A> a;
          auto pfoo = &A::foo;
          (a->*pfoo)(); // equivalent to operator->*(a, pfoo)()

      meaning the result of operator->*() must be callable: it represents a
      pending member function call.

      See Scott Meyers (though lambdas make it much easier!)
      http://www.aristeia.com/Papers/DDJ_Oct_1999.pdf
    */
    template< typename ReturnType, typename...Args, typename T = Type >
    constexpr auto operator->*(ReturnType(T::*pmf)(Args...)) const {
        return [ptr = ptr_, pmf](Args... args)
          { return (ptr->*pmf)(std::forward<Args>(args)...); };
    }
    template< typename ReturnType, typename...Args, typename T = Type>
    constexpr auto operator->*(ReturnType(T::*pmf)(Args...) const) const {
        return [ptr = ptr_, pmf](Args... args)
          { return (ptr->*pmf)(std::forward<Args>(args)...); };
    }
    template< typename MemType, typename T = Type>
    constexpr MemType operator->*(MemType T::*pm) const {
        return ptr_->*pm;
    }
#endif

    /*
      Just as bare pointers are forward and reverse iterators, so should be
      NonOwningPtrs.  Support this through prefix and postfix operator++
      and operator--, as well as operator+= and operator-=.

      Note to the implementer: the comma operator is used to meet the
      single-expression requirement on constexpr functions in C++11.
    */
    constexpr NonOwningPtr& operator++() noexcept { return ++ptr_, *this; }
    constexpr NonOwningPtr operator++(int) noexcept { return ptr_++; }
    constexpr NonOwningPtr& operator+=(std::ptrdiff_t n) noexcept {
        return ptr_ += n, *this;
    }

    constexpr NonOwningPtr& operator--() noexcept { return --ptr_, *this; }
    constexpr NonOwningPtr operator--(int) noexcept { return ptr_--; }
    constexpr NonOwningPtr& operator-=(std::ptrdiff_t n) noexcept {
        return ptr_ -= n, *this;
    }

private:
    Type * ptr_{ nullptr };
};

template< typename T >
constexpr T* get(NonOwningPtr<T> ptr) noexcept { return ptr.get(); }

/*
  A pointer is also a RandomAccessIterator, so it makes sense to provide
  operator+ and operator-.

  Note that the parameters are by value, instead of by reference.  Performance
  shouldn't be impacted, since NonOwningPtr is small.  If profiling shows that
  this should be const &, then it can be changed at a later date.
*/
template< typename T > constexpr
NonOwningPtr<T> operator+(NonOwningPtr<T> lhs, std::ptrdiff_t rhs) noexcept
    { return lhs.get() + rhs; }
template< typename T > constexpr
NonOwningPtr<T> operator+(std::ptrdiff_t lhs, NonOwningPtr<T> rhs) noexcept
    { return lhs + rhs.get(); }

template< typename T > constexpr
NonOwningPtr<T> operator-(NonOwningPtr<T> lhs, std::ptrdiff_t rhs) noexcept
    { return lhs.get() - rhs; }
template< typename T > constexpr
std::ptrdiff_t operator-(NonOwningPtr<T> lhs, NonOwningPtr<T> rhs) noexcept
    { return lhs.get() - rhs.get(); }

/*
  Make sure mixed-mode calls make the right conversions.  Without this, the
  compiler will try to do a comparison through implicit conversion to void *.
  Also, these will produce a compilation error if the comparison between raw
  pointer types wouldn't be valid, citing "comparison between distinct pointer
  types lacks a cast".

  Going through comparable_helper allows us to check whether the call would
  succeed using a SFINAE context, like this:

      std::is_same<decltype(
          std::declval<NonOwningPtr<int>>() == std::declval<double*>()
      ), bool>::value

  Value will be false in this case since the comparison isn't valid, and will
  return the type comparable_helper::not_comparable, which isn't the same as
  bool (see nonowning-detail.hpp).

  TODO: explain this better
*/
#define returns(expr) -> decltype(expr) { return expr; }

#define MIXED_MODE_NONOWNING_OPERATOR(oper, name)                       \
    template< typename Type1, typename Type2 >                          \
    auto operator oper(NonOwningPtr<Type1> lhs, NonOwningPtr<Type2> rhs) \
      returns(nown_detail::comparable_helper::name(lhs.get(), rhs.get(), bool())); \
                                                                        \
    template< typename Type1, typename Type2 >                          \
    auto operator oper(NonOwningPtr<Type1> lhs , Type2 * rhs)    \
      returns(nown_detail::comparable_helper::name(lhs.get(), rhs, bool())); \
                                                                        \
    template< typename Type1, typename Type2 >                          \
    auto operator oper(Type1 * lhs, NonOwningPtr<Type2> rhs)     \
      returns(nown_detail::comparable_helper::name(lhs, rhs.get(), bool()));

#define MIXED_MODE_WITH_NULLPTR_NONOWNING_OPERATOR(oper, name)          \
    MIXED_MODE_NONOWNING_OPERATOR(oper, name);                          \
    template< typename Type >                                           \
    auto operator oper(NonOwningPtr<Type> lhs, std::nullptr_t)   \
      returns(lhs.get() oper nullptr);                                  \
                                                                        \
    template< typename Type >                                           \
    auto operator oper(std::nullptr_t, NonOwningPtr<Type> rhs)   \
      returns(nullptr oper rhs.get());

MIXED_MODE_WITH_NULLPTR_NONOWNING_OPERATOR(==, eq);
MIXED_MODE_WITH_NULLPTR_NONOWNING_OPERATOR(!=, ne);
MIXED_MODE_NONOWNING_OPERATOR(<, lt);
MIXED_MODE_NONOWNING_OPERATOR(<=, le);
MIXED_MODE_NONOWNING_OPERATOR(>, gt);
MIXED_MODE_NONOWNING_OPERATOR(>=, ge);

#undef MIXED_MODE_WITH_NULLPTR_NONOWNING_OPERATOR
#undef MIXED_MODE_NONOWNING_OPERATOR
#undef returns

} // namespace nown

namespace std {

template<typename T> struct
  remove_pointer<nown::NonOwningPtr<T>> { using type = T; };
template<typename T> struct
  remove_pointer<nown::NonOwningPtr<T> const> { using type = T; };
template<typename T> struct
  remove_pointer<nown::NonOwningPtr<T> volatile> { using type = T; };
template<typename T> struct
  remove_pointer<nown::NonOwningPtr<T> const volatile> { using type = T; };

template< typename T > struct
  iterator_traits< nown::NonOwningPtr<T> > : iterator_traits<T*>
    { using pointer = nown::NonOwningPtr<T>; };

} // namespace std

#endif // NONOWNING_HPP
