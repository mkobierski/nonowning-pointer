
// Copyright (c) 2018, Michael Kobierski
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)

#ifndef NONOWNING_HPP
#define NONOWNING_HPP

#include "nonowning-detail.hpp"

#include <cstddef> // std::nullptr_t
#include <type_traits>
#include <utility>

namespace nown { // nonowning

template< typename T > class NonOwning;

template< typename Type >
class NonOwning<Type *> {
    class delete_ambiguifier;

    enum { is_const = std::is_const<Type>::value };
    using void_type = typename std::conditional<
        is_const, const void, void
        >::type;

public:
    using PointeeType = Type;

    constexpr NonOwning(Type * ptr = nullptr) noexcept // non-explicit
      : ptr_(ptr) { }

    constexpr NonOwning(NonOwning const & other) noexcept = default;
    constexpr NonOwning(NonOwning&& other) noexcept = default;

    constexpr NonOwning& operator=(NonOwning const & other) noexcept = default;
    constexpr NonOwning& operator=(NonOwning&& other) noexcept = default;

    template<
        typename OtherType,
        typename = typename std::enable_if<
            std::is_convertible<OtherType *, Type *>::value
            >::type
        >
    constexpr NonOwning(NonOwning<OtherType *> const & other) noexcept
      : ptr_(other.ptr_) { }

    constexpr operator bool() const noexcept { return ptr_; }

    constexpr operator Type * () const noexcept { return ptr_; }
    constexpr operator delete_ambiguifier const * () const noexcept { return nullptr; }
    constexpr operator void_type * () const noexcept { return ptr_; }

	constexpr Type * get() const noexcept { return ptr_; }
    constexpr Type * operator->() const noexcept { return ptr_; }
    constexpr Type & operator*() const noexcept { return *ptr_; }

#ifdef _MSC_VER
    // These shouldn't be required because e1->*e2 should be equivalent to
    // the expression (*e1).*e2, and we already provide operator*().  However,
    // unless we provide these, MSVC will not compile expressions involving ->*.
    template< typename ReturnType, typename...Args >
	constexpr auto operator->*(ReturnType(Type::*pmf)(Args...)) const {
		return [ptr = ptr_, pmf](Args... args)
		  { return (ptr->*pmf)(std::forward<Args>(args)...); };
	}
	template< typename ReturnType, typename...Args >
	constexpr auto operator->*(ReturnType(Type::*pmf)(Args...) const) const {
		return [ptr = ptr_, pmf](Args... args)
		  { return (ptr->*pmf)(std::forward<Args>(args)...); };
	}
	template< typename MemType >
	constexpr MemType operator->*(MemType Type::*pm) const {
		return ptr_->*pm;
	}
#endif

    void operator++() noexcept { ++ptr_; }
    NonOwning operator++(int) noexcept { return ptr_++; }

    void operator--() noexcept { --ptr_; }
    NonOwning operator--(int) noexcept { return ptr_--; }

    template<typename> friend class NonOwning;

private:
    Type * ptr_;
};

template< typename T >
T* get(NonOwning<T*> const & ptr) noexcept { return ptr.get(); }

template< typename PtrType, typename IntType >
NonOwning<PtrType *> operator+(NonOwning<PtrType *> const & lhs, IntType rhs)
  noexcept {
    return lhs.get() + rhs;
}
template< typename PtrType, typename IntType >
NonOwning<PtrType *> operator+(IntType lhs, NonOwning<PtrType *> const & rhs)
  noexcept {
    return lhs + rhs.get();
}

template< typename PtrType, typename IntType >
NonOwning<PtrType *> operator-(NonOwning<PtrType *> const & lhs, IntType rhs) noexcept {
    return lhs.get() - rhs;
}
template< typename PtrType, typename IntType >
NonOwning<PtrType *> operator-(IntType lhs, NonOwning<PtrType *> const & rhs) noexcept {
    return lhs - rhs.get();
}

#define returns(expr) -> decltype(expr) { return expr; }

#define MIXED_MODE_NONOWNING_OPERATOR(oper, name)                       \
    template< typename Type1, typename Type2 >                          \
    auto operator oper(NonOwning<Type1 *> const & lhs, NonOwning<Type2 *> const & rhs) \
      returns(nown_detail::comparable_helper::name(lhs.get(), rhs.get(), bool())); \
                                                                        \
    template< typename Type1, typename Type2 >                          \
    auto operator oper(NonOwning<Type1 *> const & lhs , Type2 * rhs)    \
      returns(nown_detail::comparable_helper::name(lhs.get(), rhs, bool())); \
                                                                        \
    template< typename Type1, typename Type2 >                          \
    auto operator oper(Type1 * lhs, NonOwning<Type2 *> const & rhs)     \
      returns(nown_detail::comparable_helper::name(lhs, rhs.get(), bool()));

#define MIXED_MODE_WITH_NULLPTR_NON_OWNING_OPERATOR(oper, name)         \
    MIXED_MODE_NONOWNING_OPERATOR(oper, name);                          \
    template< typename Type >                                           \
    auto operator oper(NonOwning<Type *> const & lhs, std::nullptr_t)   \
      returns(lhs.get() oper nullptr);                                    \
                                                                        \
    template< typename Type >                                           \
    auto operator oper(std::nullptr_t, NonOwning<Type *> const & rhs)   \
      returns(nullptr oper rhs.get());


MIXED_MODE_WITH_NULLPTR_NON_OWNING_OPERATOR(==, eq);
MIXED_MODE_WITH_NULLPTR_NON_OWNING_OPERATOR(!=, ne);
MIXED_MODE_NONOWNING_OPERATOR(<, lt);
MIXED_MODE_NONOWNING_OPERATOR(<=, le);
MIXED_MODE_NONOWNING_OPERATOR(>, gt);
MIXED_MODE_NONOWNING_OPERATOR(>=, ge);

#undef MIXED_MODE_WITH_NULLPTR_NON_OWNING_OPERATOR
#undef MIXED_MODE_NON_OWNING_OPERATOR
#undef gives

} // namespace nown

namespace std {

template<typename T> struct
  remove_pointer<nown::NonOwning<T*>> { using type = T; };
template<typename T> struct
  remove_pointer<nown::NonOwning<T*> const> { using type = T; };
template<typename T> struct
  remove_pointer<nown::NonOwning<T*> volatile> { using type = T; };
template<typename T> struct
  remove_pointer<nown::NonOwning<T*> const volatile> { using type = T; };

} // namespace std

#endif // NONOWNING_HPP
