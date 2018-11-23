
// Copyright (c) 2018, Michael Kobierski
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)

#include "nonowning.hpp"
#include "status.hpp"
#include "assert-tools.hpp"

#include <cstdint>
#include <type_traits>
#include <exception>
#include <cassert>
#include <iostream>
#include <memory>
#include <utility>

using namespace std;
using namespace nown;

namespace detail {
class A {
public:
    void foo(uint32_t bit) {
        bits_ |= bit;
    }

    void foo(uint32_t bit) const {
        constbits_ |= bit;
    }

    uint32_t bits() { return bits_; }
    uint32_t bits() const { return constbits_; }

    void reset_bits() { bits_ = constbits_ = 0u; }

    const int fourty_two = 42;

private:
    uint32_t bits_{ };
    mutable uint32_t constbits_{ };
};

class B { }; // unrelated to A

}

template< bool > struct ConstRequired { };

template< typename void_type = void, typename PtrType >
Status test_void_compatibility(PtrType ptr) {
    cout << "  test_void_compatability" << "\n";
    void_type * vptr = ptr; // test semantics against void ptr
    assert(ptr == vptr);
    assert(!(ptr != vptr));
    assert(!(ptr < vptr));
    assert(!(ptr > vptr));
    assert(ptr <= vptr);
    assert(ptr >= vptr);

    assert(vptr == ptr);
    assert(!(vptr != ptr));
    assert(!(vptr < ptr));
    assert(!(vptr > ptr));
    assert(vptr <= ptr);
    assert(vptr >= ptr);

    return Status::ok();
}

template< typename PtrType >
Status test_void_compatibility(PtrType ptr, ConstRequired<false>) {
    cout << " test_void_compatability(non-const)" << "\n";
    test_void_compatibility(ptr);
    test_void_compatibility(ptr, ConstRequired<true>());
    return Status::ok();
}
template< typename PtrType >
Status test_void_compatibility(PtrType ptr, ConstRequired<true>) {
    cout << "  test_void_compatability(const)" << "\n";
    test_void_compatibility<void const>(ptr);
    return Status::ok();
}

template< typename PtrType >
void test_inc_and_dec(PtrType ptr) {
    cout << " test_inc_and_dec" << "\n";
    void const * vptr = ptr;
    auto orig_val = ptr++; ++ptr;
    const int times_incremented = 2;
    assert(ptr == (void const *)(times_incremented + orig_val));
    assert(ptr == (void const *)(orig_val + times_incremented));
    assert((ptr - times_incremented) == orig_val);
    assert(orig_val == (ptr - times_incremented));
    assert(!(ptr != (void const *)(orig_val + times_incremented) ));
    assert(ptr > vptr);
    assert(!(ptr <= vptr));
    assert(ptr != vptr);
    assert(!(ptr == vptr));

    assert((void const *)(times_incremented + orig_val) == ptr);
    assert((void const *)(orig_val + times_incremented) == ptr);
    assert(!((void const *)(orig_val + times_incremented) != ptr));
    assert(vptr < ptr);
    assert(!(vptr > ptr));
    assert(!(vptr >= ptr));
    assert(vptr <= ptr);

    auto incremented = ptr--; --ptr;
    assert(vptr == incremented - times_incremented);
    assert(ptr == vptr);

    // shouldn't be able to add pointers.

}

template< typename PtrType >
Status test_auto_compatibility(PtrType ptr) {
    cout << " test_auto_compatability" << "\n";
    auto copy = ptr;
    assert(ptr == copy);
    assert(!(ptr != copy));
    assert(!(ptr < copy));
    assert(!(ptr > copy));
    assert(ptr <= copy);
    assert(ptr >= copy);
    return Status::ok();
}

template< typename PtrType >
void test_dereference(PtrType ptr) {
    cout << " test_dereference" << "\n";
    uint32_t bit = 1;

    ptr->foo(bit);

    bit <<= 1;

    (*ptr).foo(bit);

    bit <<= 1;
    using PointeeType = std::remove_pointer_t<PtrType>;
    using FuncType = std::conditional_t<std::is_const<PointeeType>::value,
        void (PointeeType::*)(uint32_t) const,
        void (PointeeType::*)(uint32_t)>;

    FuncType pfoo = &PointeeType::foo;
    (ptr->*pfoo)(bit);

    const int PointeeType::*pmem = &PointeeType::fourty_two;
    assert(ptr->*pmem == 42);

    uint32_t expected = 0b111u;
    assert(expected == ptr->bits());
}

template< typename PtrType >
void test_conv_to_bool(PtrType ptr) {
    cout << " test_conv_to_bool" << "\n";
    assert(bool(ptr));
    if(ptr) { } else { assert(false); }
    if(!ptr) {
        assert(false);
    }
}

template< typename PrototypePointee >
Status test_pointer() {
    cout << "test_pointer" << endl;
    using namespace detail;

    {
        auto owner_a1 = make_unique<A>();
        auto owner_a2 = make_unique<A>();

        constexpr bool prototype_is_const = is_const<PrototypePointee>::value;

        using PointeeType = conditional_t<prototype_is_const, A const, A>;

        PointeeType * na = owner_a1.get();
        NonOwning<PointeeType*> noa = owner_a2.get();

        test_dereference(na);
        test_dereference(noa);

        test_void_compatibility(na, ConstRequired<prototype_is_const>());
        test_void_compatibility(noa, ConstRequired<prototype_is_const>());

        test_inc_and_dec(na);
        test_inc_and_dec(noa);

        test_auto_compatibility(na);
        test_auto_compatibility(noa);

        test_conv_to_bool(na);
        test_conv_to_bool(noa);

        auto na2 = na;
        assert(na2 == na);
        assert(!(na2 != na));

        auto noa2 = noa;
        assert(noa2 == noa);
        assert(!(noa2 != noa));

        A a_dummy;

        A const * cna = na;
        assert(cna == na);
        cna = &a_dummy;
        assert(cna != na);

        B b_dummy;
        B * b = &b_dummy; (void) b;
        A * a = &a_dummy; (void) a;
        ASSERT_DOESNT_COMPILE(a != dependent(b));
    }
    return Status::ok();
}

Status test_copy_and_move() {
    using namespace detail;
    {
        auto a = make_unique<A>();
        NonOwning<A*> nopa = a.get();
        ASSERT_DELETE_DOESNT_COMPILE(nopa);

        NonOwning<A*> const cnopa = nopa;
        ASSERT_DELETE_DOESNT_COMPILE(cnopa);

        NonOwning<A const *> nopca1 = nopa; (void)nopca1;
        ASSERT_DELETE_DOESNT_COMPILE(nopca1);

        NonOwning<A const *> nopca2 = a.get(); (void)nopca2;
        ASSERT_DELETE_DOESNT_COMPILE(nopca1);

        NonOwning<A const *> const cnopca = cnopa; (void)cnopca;
        ASSERT_DELETE_DOESNT_COMPILE(nopca2);
    }
    {
        auto a = make_unique<A>();
        NonOwning<A*> nopa = a.get();
        auto copy = nopa;
        NonOwning<A*> const cnopa = move(copy);
        NonOwning<A const *> nopca1 = move(nopa); (void)nopca1;
        NonOwning<A const *> nopca2 = a.get(); (void)nopca2;
        NonOwning<A const *> const cnopca = move(cnopa); (void)cnopca;
    }

    struct NewA : A { };
    struct Unrelated;

    NonOwning<NewA*> nopna = nullptr;
    NonOwning<A*> nopa = nopna; (void)nopa;
    ASSERT_DOESNT_COMPILE( NonOwning<Unrelated*>(dependent(nopa)) );

    return Status::ok();
}

namespace test_call_detail {

class Tester {
public:
    enum class opt {
        unset, func_tip, cfunc_tip, overloaded_non_const_tip,
        overloaded_const_tip, tfunc_non_const_tip,
        tfunc_const_tip };
    opt get_and_reset() { auto tmp = data_; data_ = opt::unset; return tmp; }
    void set(opt the_opt) { data_ = the_opt; }
    void set_from(detail::A*) { data_ = opt::tfunc_non_const_tip; }
    void set_from(detail::A const *) { data_ = opt::tfunc_const_tip; }

private:
    opt data_;
};

void func(detail::A *, Tester & t) { t.set(Tester::opt::func_tip); }
void cfunc(detail::A const *, Tester & t) { t.set(Tester::opt::cfunc_tip); }

template< typename T >
void tfunc(T * param, Tester & t) { t.set_from(param); }

void overloaded(detail::A *, Tester & t) {
    t.set(Tester::opt::overloaded_non_const_tip); }
void overloaded(detail::A const *, Tester & t) {
    t.set(Tester::opt::overloaded_const_tip); }

} // namespace test_call_detail

Status test_call() {
    using namespace detail;
    using namespace test_call_detail;
    {
        auto a = make_unique<A>();
        NonOwning<A*> nopa = a.get();
        ASSERT_DELETE_DOESNT_COMPILE(nopa);

        NonOwning<A*> const cnopa = nopa;
        ASSERT_DELETE_DOESNT_COMPILE(cnopa);

        NonOwning<A const *> nopca = nopa; (void)nopca;
        ASSERT_DELETE_DOESNT_COMPILE(nopca);

        Tester t;
        using opt = Tester::opt;
        opt result = opt::unset;

        func(nopa, t);
        result = t.get_and_reset();
        assert(result == opt::func_tip);

        cfunc(cnopa, t);
        result = t.get_and_reset();
        assert(result == opt::cfunc_tip);

        overloaded(nopa, t);
        result = t.get_and_reset();
        assert(result == opt::overloaded_non_const_tip);

        overloaded(nopca, t);
        result = t.get_and_reset();
        assert(result == opt::overloaded_const_tip);

        tfunc(get(nopa), t);
        result = t.get_and_reset();
        assert(result == opt::tfunc_non_const_tip);

        tfunc(get(cnopa), t);
        result = t.get_and_reset();
        assert(result == opt::tfunc_non_const_tip);

        tfunc(get(nopca), t);
        result = t.get_and_reset();
        assert(result == opt::tfunc_const_tip);
    }
    return Status::ok();
}

struct expect_comparable { };
struct expect_not_comparable { };

template< typename PtrType >
Status test_mixed_comparison(PtrType ptr1, nullptr_t, expect_comparable) {
    // Cast to bool since these expressions should be usable in a bool context
    // Cast to void to avoid unused expression warnings.
    (void)(bool)(ptr1 == nullptr);
    (void)(bool)(ptr1 != nullptr);
    return Status::ok();
}

template< typename PtrType >
Status test_mixed_comparison(nullptr_t, PtrType ptr2, expect_comparable) {
    // Cast to bool since these expressions should be usable in a bool context
    // Cast to void to avoid unused expression warnings.
    (void)(bool)(nullptr == ptr2);
    (void)(bool)(nullptr != ptr2);
    return Status::ok();
}

template< typename PtrType1, typename PtrType2 >
Status test_mixed_comparison(PtrType1 ptr1, PtrType2 ptr2, expect_comparable) {
    (void)(bool)(ptr1 == ptr2);
    (void)(bool)(ptr1 != ptr2);
    (void)(bool)(ptr1 < ptr2);
    (void)(bool)(ptr1 > ptr2);
    (void)(bool)(ptr1 <= ptr2);
    (void)(bool)(ptr1 >= ptr2);
    return Status::ok();
}

template< typename PtrType1, typename PtrType2 >
Status test_mixed_comparison(PtrType1 ptr1, PtrType2 ptr2, expect_not_comparable) {
    // Cast to bool since these expressions should be usable in a bool context
    //
    // In our case, if PtrType is NonOwning<Something*> and the mixed comparison
    // will result in a comparison between incompatible pointer types, the
    // result of the expression is of type comparable_helper::not_comparable,
    // which is not convertible to bool.  By casting to bool here, we are able
    // to figure this out "early".  Note that comparison between incompatible
    // pointer types will compile so long as the result is not used, however
    // will not link: the would-be invalid comparison function does not provide
    // a definition.
    //
    ASSERT_DOESNT_COMPILE((bool)(ptr1 == dependent(ptr2)));
    ASSERT_DOESNT_COMPILE((bool)(ptr1 != dependent(ptr2)));
    ASSERT_DOESNT_COMPILE((bool)(ptr1 < dependent(ptr2)));
    ASSERT_DOESNT_COMPILE((bool)(ptr1 > dependent(ptr2)));
    ASSERT_DOESNT_COMPILE((bool)(ptr1 <= dependent(ptr2)));
    ASSERT_DOESNT_COMPILE((bool)(ptr1 >= dependent(ptr2)));
    return Status::ok();
}

Status test_mixed_types() {
    cout << "test_mixed_types" << "\n";
    using namespace detail;

    {
        auto a_owner = make_unique<A>();
        auto b_owner = make_unique<B>();

        A * a = a_owner.get();
        B * b = b_owner.get();

        NonOwning<A *> na = a;
        NonOwning<B *> nb = b;

        test_mixed_comparison(a, b, expect_not_comparable());
        test_mixed_comparison(na, nb, expect_not_comparable());

        test_mixed_comparison(a, na, expect_comparable());

        test_mixed_comparison(a, nb, expect_not_comparable());
        test_mixed_comparison(nb, a, expect_not_comparable());

        test_mixed_comparison(a, nullptr, expect_comparable());
        test_mixed_comparison(nullptr, a, expect_comparable());

        struct BB : B { };

        auto bb_owner = make_unique<BB>();
        BB * bb = bb_owner.get();
        NonOwning<BB *> nbb = bb;
        (void) nbb;

        assert(bb != b);
        ASSERT_DOESNT_COMPILE(bb == dependent(a));

        assert(nbb != nb);
        ASSERT_DOESNT_COMPILE((bool)(nbb == dependent(na)));

        assert(nbb != b);
        assert(b != nbb);
        ASSERT_DOESNT_COMPILE((bool)(nbb == dependent(a)));
        ASSERT_DOESNT_COMPILE((bool)(a == dependent(nbb)));

        ASSERT_DOESNT_COMPILE(NonOwning<B *>(dependent(a)));
        ASSERT_DOESNT_COMPILE(NonOwning<B *>(dependent(na)));
        NonOwning<B *> nb2 = b;
        nb2 = b;
        NonOwning<B *> nb3 = nb;
        nb3 = nb;
        NonOwning<B *> nb4 = nbb;
        nb4 = nbb;
        NonOwning<B const *> nb5 = nbb;
        nb5 = nbb;
        NonOwning<BB const *> ncbb = nbb;
        ncbb = nbb;

        ASSERT_DOESNT_COMPILE(NonOwning<BB *>(dependent(ncbb)));
        NonOwning<BB*> nbb2;
        ASSERT_DOESNT_COMPILE(nbb2 = dependent(ncbb));
        ASSERT_DOESNT_COMPILE(NonOwning<B *>(dependent(ncbb)));
        NonOwning<B *> nb6;
        ASSERT_DOESNT_COMPILE(nb6 = dependent(ncbb));

        struct BBx : B { };
        NonOwning<BBx*> nbbx;
        ASSERT_DOESNT_COMPILE((bool)(nbbx == dependent(nbb)));


        void * vptr = nb; vptr = nb;
        void const * cvptr = nb; (void)(cvptr = nb);
        B * back_to_normal = nb; (void)(back_to_normal = nb);

		class Invisible;
        NonOwning<Invisible *> invis;
        NonOwning<Invisible const *> cinvis;

		ASSERT_DELETE_DOESNT_COMPILE(invis);
		ASSERT_DELETE_DOESNT_COMPILE(cinvis);

        auto func = [](Invisible *) { };
        auto cfunc = [](Invisible const *) { };
        func(invis);

        ASSERT_DOESNT_COMPILE(func(dependent(cinvis)));

        cfunc(cinvis);
        cfunc(invis);

        vptr = invis;
        ASSERT_DOESNT_COMPILE(vptr = dependent(cinvis));

    }
    return Status::ok();
}

Status test_swap() {
    using std::swap;

    using namespace detail;

    A a_dummy;
    NonOwning<A*> a1 = &a_dummy;
    NonOwning<A*> a2;
    swap(a1, a2);
    assert(a1 == nullptr);
    assert(a2 == &a_dummy);

    return Status::ok();
}

int main() {
    try {
        check(test_mixed_types());
        check(test_pointer<void>());
        check(test_pointer<void const>());
        check(test_call());
        check(test_copy_and_move());
        check(test_swap());
    }
    catch(exception & exc) {
        cout << "Exception caught." << endl;
        cout << exc.what();
    }

    return 0;
}