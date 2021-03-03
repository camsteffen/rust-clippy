use crate::approx_const::ApproxConstant;
use crate::arithmetic::Arithmetic;
use crate::as_conversions::AsConversions;
use crate::asm_syntax::InlineAsmX86AttSyntax;
use crate::asm_syntax::InlineAsmX86IntelSyntax;
use crate::assertions_on_constants::AssertionsOnConstants;
use crate::assign_ops::AssignOps;
use crate::async_yields_async::AsyncYieldsAsync;
use crate::atomic_ordering::AtomicOrdering;
use crate::attrs::Attributes;
use crate::await_holding_invalid::AwaitHolding;
use crate::blocks_in_if_conditions::BlocksInIfConditions;
use crate::booleans::NonminimalBool;
use crate::bytecount::ByteCount;
use crate::case_sensitive_file_extension_comparisons::CaseSensitiveFileExtensionComparisons;
use crate::collapsible_if::CollapsibleIf;
use crate::collapsible_match::CollapsibleMatch;
use crate::comparison_chain::ComparisonChain;
use crate::copies::CopyAndPaste;
use crate::copy_iterator::CopyIterator;
use crate::create_dir::CreateDir;
use crate::default::Default as DefaultLint;
use crate::default_numeric_fallback::DefaultNumericFallback;
use crate::dereference::Dereferencing;
use crate::derive::Derive;
use crate::double_comparison::DoubleComparisons;
use crate::double_parens::DoubleParens;
use crate::drop_forget_ref::DropForgetRef;
use crate::duration_subsec::DurationSubsec;
use crate::else_if_without_else::ElseIfWithoutElse;
use crate::empty_enum::EmptyEnum;
use crate::entry::HashMapPass;
use crate::enum_clike::UnportableVariant;
use crate::eq_op::EqOp;
use crate::erasing_op::ErasingOp;
use crate::eta_reduction::EtaReduction;
use crate::eval_order_dependence::EvalOrderDependence;
use crate::exhaustive_items::ExhaustiveItems;
use crate::exit::Exit;
use crate::explicit_write::ExplicitWrite;
use crate::fallible_impl_from::FallibleImplFrom;
use crate::float_equality_without_abs::FloatEqualityWithoutAbs;
use crate::float_literal::FloatLiteral;
use crate::floating_point_arithmetic::FloatingPointArithmetic;
use crate::format::UselessFormat;
use crate::formatting::Formatting;
use crate::from_str_radix_10::FromStrRadix10;
use crate::future_not_send::FutureNotSend;
use crate::get_last_with_len::GetLastWithLen;
use crate::identity_op::IdentityOp;
use crate::if_let_mutex::IfLetMutex;
use crate::if_let_some_result::OkIfLet;
use crate::if_not_else::IfNotElse;
use crate::implicit_return::ImplicitReturn;
use crate::implicit_saturating_sub::ImplicitSaturatingSub;
use crate::inconsistent_struct_constructor::InconsistentStructConstructor;
use crate::indexing_slicing::IndexingSlicing;
use crate::infinite_iter::InfiniteIter;
use crate::inherent_impl::MultipleInherentImpl;
use crate::inherent_to_string::InherentToString;
use crate::inline_fn_without_body::InlineFnWithoutBody;
use crate::int_plus_one::IntPlusOne;
use crate::integer_division::IntegerDivision;
use crate::items_after_statements::ItemsAfterStatements;
use crate::len_zero::LenZero;
use crate::let_if_seq::LetIfSeq;
use crate::let_underscore::LetUnderscore;
use crate::lifetimes::Lifetimes;
use crate::loops::Loops;
use crate::macro_use::MacroUseImports;
use crate::main_recursion::MainRecursion;
use crate::manual_async_fn::ManualAsyncFn;
use crate::manual_map::ManualMap;
use crate::manual_ok_or::ManualOkOr;
use crate::manual_unwrap_or::ManualUnwrapOr;
use crate::map_clone::MapClone;
use crate::map_err_ignore::MapErrIgnore;
use crate::map_identity::MapIdentity;
use crate::map_unit_fn::MapUnit;
use crate::match_on_vec_items::MatchOnVecItems;
use crate::mem_discriminant::MemDiscriminant;
use crate::mem_forget::MemForget;
use crate::minmax::MinMaxPass;
use crate::misc::MiscLints;
use crate::misc_early::MiscEarlyLints;
use crate::missing_doc::MissingDoc;
use crate::missing_inline::MissingInline;
use crate::modulo_arithmetic::ModuloArithmetic;
use crate::multiple_crate_versions::MultipleCrateVersions;
use crate::mut_key::MutableKeyType;
use crate::mut_mut::MutMut;
use crate::mut_mutex_lock::MutMutexLock;
use crate::mut_reference::UnnecessaryMutPassed;
use crate::mutable_debug_assertion::DebugAssertWithMutCall;
use crate::mutex_atomic::Mutex;
use crate::needless_arbitrary_self_type::NeedlessArbitrarySelfType;
use crate::needless_bool::{BoolComparison, NeedlessBool};
use crate::needless_borrow::NeedlessBorrow;
use crate::needless_borrowed_ref::NeedlessBorrowedRef;
use crate::needless_continue::NeedlessContinue;
use crate::needless_pass_by_value::NeedlessPassByValue;
use crate::needless_update::NeedlessUpdate;
use crate::neg_cmp_op_on_partial_ord::NoNegCompOpForPartialOrd;
use crate::neg_multiply::NegMultiply;
use crate::new_without_default::NewWithoutDefault;
use crate::no_effect::NoEffect;
use crate::non_copy_const::NonCopyConst;
use crate::open_options::OpenOptions;
use crate::option_env_unwrap::OptionEnvUnwrap;
use crate::option_if_let_else::OptionIfLetElse;
use crate::overflow_check_conditional::OverflowCheckConditional;
use crate::panic_in_result_fn::PanicInResultFn;
use crate::panic_unimplemented::PanicUnimplemented;
use crate::partialeq_ne_impl::PartialEqNeImpl;
use crate::path_buf_push_overwrite::PathBufPushOverwrite;
use crate::pattern_type_mismatch::PatternTypeMismatch;
use crate::precedence::Precedence;
use crate::ptr::Ptr;
use crate::ptr_eq::PtrEq;
use crate::ptr_offset_with_cast::PtrOffsetWithCast;
use crate::question_mark::QuestionMark;
use crate::redundant_clone::RedundantClone;
use crate::redundant_else::RedundantElse;
use crate::redundant_pub_crate::RedundantPubCrate;
use crate::redundant_slicing::RedundantSlicing;
use crate::ref_option_ref::RefOptionRef;
use crate::reference::DerefAddrOf;
use crate::reference::RefInDeref;
use crate::regex::Regex;
use crate::repeat_once::RepeatOnce;
use crate::returns::Return;
use crate::self_assignment::SelfAssignment;
use crate::semicolon_if_nothing_returned::SemicolonIfNothingReturned;
use crate::serde_api::SerdeApi;
use crate::shadow::Shadow;
use crate::single_component_path_imports::SingleComponentPathImports;
use crate::size_of_in_element_count::SizeOfInElementCount;
use crate::slow_vector_initialization::SlowVectorInit;
use crate::stable_sort_primitive::StableSortPrimitive;
use crate::strings::{StrToString, StringAdd, StringLitAsBytes, StringToString};
use crate::suspicious_operation_groupings::SuspiciousOperationGroupings;
use crate::suspicious_trait_impl::SuspiciousImpl;
use crate::swap::Swap;
use crate::tabs_in_doc_comments::TabsInDocComments;
use crate::temporary_assignment::TemporaryAssignment;
use crate::to_digit_is_some::ToDigitIsSome;
use crate::to_string_in_display::ToStringInDisplay;
use crate::transmute::Transmute;
use crate::transmuting_null::TransmutingNull;
use crate::try_err::TryErr;
use crate::types::{
    AbsurdExtremeComparisons, Casts, CharLitAsU8, ImplicitHasher, InvalidUpcastComparisons, LetUnitValue, RefToMut,
    UnitArg, UnitCmp,
};
use crate::undropped_manually_drops::UndroppedManuallyDrops;
use crate::unicode::Unicode;
use crate::unit_return_expecting_ord::UnitReturnExpectingOrd;
use crate::unnamed_address::UnnamedAddress;
use crate::unnecessary_sort_by::UnnecessarySortBy;
use crate::unnecessary_wraps::UnnecessaryWraps;
use crate::unnested_or_patterns::UnnestedOrPatterns;
use crate::unsafe_removed_from_name::UnsafeNameRemoval;
use crate::unused_io_amount::UnusedIoAmount;
use crate::unused_self::UnusedSelf;
use crate::unused_unit::UnusedUnit;
use crate::unwrap::Unwrap;
use crate::unwrap_in_result::UnwrapInResult;
use crate::useless_conversion::UselessConversion;
use crate::utils::author::Author;
use crate::vec_init_then_push::VecInitThenPush;
use crate::vec_resize_to_zero::VecResizeToZero;
use crate::verbose_file_reads::VerboseFileReads;
use crate::wildcard_dependencies::WildcardDependencies;
use crate::zero_div_zero::ZeroDiv;
use crate::zero_sized_map_values::ZeroSizedMapValues;
use rustc_ast as ast;
use rustc_hir as hir;
use rustc_lint::LintArray;
use rustc_lint::{
    declare_combined_early_lint_pass, declare_combined_late_lint_pass, early_lint_methods,
    expand_combined_early_lint_pass_method, expand_combined_early_lint_pass_methods,
    expand_combined_late_lint_pass_method, expand_combined_late_lint_pass_methods, late_lint_methods, EarlyContext,
    EarlyLintPass, LateContext, LateLintPass, LintPass,
};
use rustc_span::symbol::Ident;
use rustc_span::{Span, Symbol};

// todo export and use `declare_combined_early_pass` instead
early_lint_methods!(declare_combined_early_lint_pass, [pub ClippyCombinedEarlyLintPass, [
    AsConversions: AsConversions,
    CollapsibleIf: CollapsibleIf,
    DerefAddrOf: DerefAddrOf,
    DoubleParens: DoubleParens,
    ElseIfWithoutElse: ElseIfWithoutElse,
    Formatting: Formatting,
    IfNotElse: IfNotElse,
    InlineAsmX86AttSyntax: InlineAsmX86AttSyntax,
    InlineAsmX86IntelSyntax: InlineAsmX86IntelSyntax,
    IntPlusOne: IntPlusOne,
    ItemsAfterStatements: ItemsAfterStatements,
    MiscEarlyLints: MiscEarlyLints,
    NeedlessArbitrarySelfType: NeedlessArbitrarySelfType,
    NeedlessContinue: NeedlessContinue,
    OptionEnvUnwrap: OptionEnvUnwrap,
    Precedence: Precedence,
    RedundantElse: RedundantElse,
    RefInDeref: RefInDeref,
    SingleComponentPathImports: SingleComponentPathImports,
    SuspiciousOperationGroupings: SuspiciousOperationGroupings,
    TabsInDocComments: TabsInDocComments,
    UnnestedOrPatterns: UnnestedOrPatterns,
    UnsafeNameRemoval: UnsafeNameRemoval,
    UnusedUnit: UnusedUnit,
]]);

late_lint_methods!(declare_combined_late_lint_pass, [pub ClippyCombinedLateLintPass, [
    AbsurdExtremeComparisons: AbsurdExtremeComparisons,
    ApproxConstant: ApproxConstant,
    Arithmetic: Arithmetic::default(),
    AssertionsOnConstants: AssertionsOnConstants,
    AssignOps: AssignOps,
    AsyncYieldsAsync: AsyncYieldsAsync,
    AtomicOrdering: AtomicOrdering,
    Attributes: Attributes,
    Author: Author,
    AwaitHolding: AwaitHolding,
    BlocksInIfConditions: BlocksInIfConditions,
    BoolComparison: BoolComparison,
    ByteCount: ByteCount,
    CaseSensitiveFileExtensionComparisons: CaseSensitiveFileExtensionComparisons,
    Casts: Casts,
    CharLitAsU8: CharLitAsU8,
    CollapsibleMatch: CollapsibleMatch,
    ComparisonChain: ComparisonChain,
    CopyAndPaste: CopyAndPaste,
    CopyIterator: CopyIterator,
    CreateDir: CreateDir,
    DebugAssertWithMutCall: DebugAssertWithMutCall,
    DefaultLint: DefaultLint::default(),
    DefaultNumericFallback: DefaultNumericFallback,
    Dereferencing: Dereferencing,
    Derive: Derive,
    DoubleComparisons: DoubleComparisons,
    DropForgetRef: DropForgetRef,
    DurationSubsec: DurationSubsec,
    EmptyEnum: EmptyEnum,
    EqOp: EqOp,
    ErasingOp: ErasingOp,
    EtaReduction: EtaReduction,
    EvalOrderDependence: EvalOrderDependence,
    ExhaustiveItems: ExhaustiveItems,
    Exit: Exit,
    ExplicitWrite: ExplicitWrite,
    FallibleImplFrom: FallibleImplFrom,
    FloatEqualityWithoutAbs: FloatEqualityWithoutAbs,
    FloatLiteral: FloatLiteral,
    FloatingPointArithmetic: FloatingPointArithmetic,
    FromStrRadix10: FromStrRadix10,
    FutureNotSend: FutureNotSend,
    GetLastWithLen: GetLastWithLen,
    HashMapPass: HashMapPass,
    IdentityOp: IdentityOp,
    IfLetMutex: IfLetMutex,
    ImplicitHasher: ImplicitHasher,
    ImplicitReturn: ImplicitReturn,
    ImplicitSaturatingSub: ImplicitSaturatingSub,
    InconsistentStructConstructor: InconsistentStructConstructor,
    IndexingSlicing: IndexingSlicing,
    InfiniteIter: InfiniteIter,
    InherentToString: InherentToString,
    InlineFnWithoutBody: InlineFnWithoutBody,
    IntegerDivision: IntegerDivision,
    InvalidUpcastComparisons: InvalidUpcastComparisons,
    LenZero: LenZero,
    LetIfSeq: LetIfSeq,
    LetUnderscore: LetUnderscore,
    LetUnitValue: LetUnitValue,
    Lifetimes: Lifetimes,
    Loops: Loops,
    MacroUseImports: MacroUseImports::default(),
    MainRecursion: MainRecursion::default(),
    ManualAsyncFn: ManualAsyncFn,
    ManualMap: ManualMap,
    ManualOkOr: ManualOkOr,
    ManualUnwrapOr: ManualUnwrapOr,
    MapClone: MapClone,
    MapErrIgnore: MapErrIgnore,
    MapIdentity: MapIdentity,
    MapUnit: MapUnit,
    MatchOnVecItems: MatchOnVecItems,
    MemDiscriminant: MemDiscriminant,
    MemForget: MemForget,
    MinMaxPass: MinMaxPass,
    MiscLints: MiscLints,
    MissingDoc: MissingDoc::new(),
    MissingInline: MissingInline,
    ModuloArithmetic: ModuloArithmetic,
    MultipleCrateVersions: MultipleCrateVersions,
    MultipleInherentImpl: MultipleInherentImpl::default(),
    MutMut: MutMut,
    MutMutexLock: MutMutexLock,
    MutableKeyType: MutableKeyType,
    Mutex: Mutex,
    NeedlessBool: NeedlessBool,
    NeedlessBorrow: NeedlessBorrow::default(),
    NeedlessBorrowedRef: NeedlessBorrowedRef,
    NeedlessPassByValue: NeedlessPassByValue,
    NeedlessUpdate: NeedlessUpdate,
    NegMultiply: NegMultiply,
    NewWithoutDefault: NewWithoutDefault::default(),
    NoEffect: NoEffect,
    NoNegCompOpForPartialOrd: NoNegCompOpForPartialOrd,
    NonCopyConst: NonCopyConst,
    NonminimalBool: NonminimalBool,
    OkIfLet: OkIfLet,
    OpenOptions: OpenOptions,
    OptionIfLetElse: OptionIfLetElse,
    OverflowCheckConditional: OverflowCheckConditional,
    PanicInResultFn: PanicInResultFn,
    PanicUnimplemented: PanicUnimplemented,
    PartialEqNeImpl: PartialEqNeImpl,
    PathBufPushOverwrite: PathBufPushOverwrite,
    PatternTypeMismatch: PatternTypeMismatch,
    Ptr: Ptr,
    PtrEq: PtrEq,
    PtrOffsetWithCast: PtrOffsetWithCast,
    QuestionMark: QuestionMark,
    RedundantClone: RedundantClone,
    RedundantPubCrate: RedundantPubCrate::default(),
    RedundantSlicing: RedundantSlicing,
    RefOptionRef: RefOptionRef,
    RefToMut: RefToMut,
    Regex: Regex::default(),
    RepeatOnce: RepeatOnce,
    Return: Return,
    SelfAssignment: SelfAssignment,
    SemicolonIfNothingReturned: SemicolonIfNothingReturned,
    SerdeApi: SerdeApi,
    Shadow: Shadow,
    SizeOfInElementCount: SizeOfInElementCount,
    SlowVectorInit: SlowVectorInit,
    StableSortPrimitive: StableSortPrimitive,
    StrToString: StrToString,
    StringAdd: StringAdd,
    StringLitAsBytes: StringLitAsBytes,
    StringToString: StringToString,
    SuspiciousImpl: SuspiciousImpl,
    Swap: Swap,
    TemporaryAssignment: TemporaryAssignment,
    ToDigitIsSome: ToDigitIsSome,
    ToStringInDisplay: ToStringInDisplay::new(),
    Transmute: Transmute,
    TransmutingNull: TransmutingNull,
    TryErr: TryErr,
    UndroppedManuallyDrops: UndroppedManuallyDrops,
    Unicode: Unicode,
    UnitArg: UnitArg,
    UnitCmp: UnitCmp,
    UnitReturnExpectingOrd: UnitReturnExpectingOrd,
    UnnamedAddress: UnnamedAddress,
    UnnecessaryMutPassed: UnnecessaryMutPassed,
    UnnecessarySortBy: UnnecessarySortBy,
    UnnecessaryWraps: UnnecessaryWraps,
    UnportableVariant: UnportableVariant,
    UnusedIoAmount: UnusedIoAmount,
    UnusedSelf: UnusedSelf,
    Unwrap: Unwrap,
    UnwrapInResult: UnwrapInResult,
    UselessConversion: UselessConversion::default(),
    UselessFormat: UselessFormat,
    VecInitThenPush: VecInitThenPush::default(),
    VecResizeToZero: VecResizeToZero,
    VerboseFileReads: VerboseFileReads,
    WildcardDependencies: WildcardDependencies,
    ZeroDiv: ZeroDiv,
    ZeroSizedMapValues: ZeroSizedMapValues,
]], ['tcx]);
