use std::mem::replace;

use proc_macro::TokenStream;
use quote::ToTokens;
use syn::{
    parse_quote_spanned,
    spanned::Spanned,
    visit_mut::{
        visit_expr_if_mut, visit_expr_match_mut, visit_expr_while_mut,
        VisitMut,
    },
    BinOp, Error, Expr, ExprBinary, ExprIf, ExprMatch, ExprUnary, ExprWhile,
    ImplItem, UnOp,
};

fn weak(expr: &mut Expr) {
    let local = replace(expr, Expr::PLACEHOLDER);

    *expr = parse_quote_spanned! { expr.span() =>
        ::weak_true::WeakTrue::weak_true(&#local)
    };
}

fn try_weak_true_cond(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(ExprBinary {
            op: BinOp::And(_) | BinOp::Or(_),
            left,
            right,
            ..
        }) => {
            weak_true_cond(left);
            weak_true_cond(right);
            true
        },
        Expr::Unary(ExprUnary { op: UnOp::Not(_), expr, .. }) => {
            weak_true_cond(expr);
            true
        },
        _ => false,
    }
}

fn weak_true_cond(expr: &mut Expr) {
    if !try_weak_true_cond(expr) {
        weak(expr);
    }
}

struct Visitor;

impl VisitMut for Visitor {
    fn visit_expr_if_mut(&mut self, node: &mut ExprIf) {
        weak_true_cond(&mut node.cond);
        visit_expr_if_mut(self, node);
    }
    fn visit_expr_while_mut(&mut self, node: &mut ExprWhile) {
        weak_true_cond(&mut node.cond);
        visit_expr_while_mut(self, node);
    }
    fn visit_expr_match_mut(&mut self, node: &mut ExprMatch) {
        for arm in &mut node.arms {
            if let Some((_, guard)) = &mut arm.guard {
                weak_true_cond(guard);
            }
        }
        visit_expr_match_mut(self, node);
    }
}

#[proc_macro_attribute]
pub fn weak_true(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(tt) = attr.into_iter().next() {
        return Error::new(tt.span().into(), "invalid token")
            .into_compile_error()
            .into();
    }

    let mut item = match syn::parse::<ImplItem>(item) {
        Ok(item) => item,
        Err(e) => return e.into_compile_error().into(),
    };

    Visitor.visit_impl_item_mut(&mut item);

    item.into_token_stream().into()
}
