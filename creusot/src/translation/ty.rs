use rustc_middle::ty::{self, subst::InternalSubsts, AdtDef, Ty, TyCtxt, TyKind::*};

use crate::mlcfg::{MlCfgType as MlT, MlTyDecl};

pub struct TyTranslator<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TyTranslator<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        TyTranslator { tcx }
    }

    pub fn translate_tydecl(&self, adt: &AdtDef) -> MlTyDecl {
        let gens = self.tcx.generics_of(adt.did);

        let ty_args: Vec<_> = gens
            .params
            .iter()
            .filter_map(|param| match param.kind {
                ty::GenericParamDefKind::Type { .. } => Some(param.name.to_string()),
                _ => None,
            })
            .collect();

        let substs = InternalSubsts::identity_for_item(self.tcx, adt.did);

        let mut ml_ty_def = Vec::new();

        for var_def in adt.variants.iter() {
            let field_tys: Vec<_> = var_def
                .fields
                .iter()
                .map(|f| f.ty(self.tcx, substs))
                .map(|ty| self.translate_ty(ty))
                .collect();
            log::debug!("{:?}({:?})", var_def.ident, field_tys);

            ml_ty_def.push((var_def.ident.to_string(), field_tys));
        }

        let ty_name =
            super::translate_defid(self.tcx, adt.did).split('.').last().unwrap().to_string();
        MlTyDecl { ty_name, ty_params: ty_args, ty_constructors: ml_ty_def }
    }

    pub fn translate_ty(&self, ty: Ty<'tcx>) -> MlT {
        match ty.kind() {
            Bool => MlT::Bool,
            Char => unimplemented!(),
            Int(ity) => MlT::Int(*ity),
            Uint(uity) => MlT::Uint(*uity),
            Float(_) => unimplemented!(),
            Adt(def, s) => {
                if def.is_box() {
                    return self.translate_ty(s[0].expect_ty());
                }
                let args = s.types().map(|t| self.translate_ty(t)).collect();

                MlT::TApp(box MlT::TConstructor(super::translate_defid(self.tcx, def.did)), args)
            }
            Str => unimplemented!("str"),
            Array(_, _) => unimplemented!("array"),
            Slice(_) => unimplemented!("slice"),
            Tuple(args) => {
                let tys = args.types().map(|t| self.translate_ty(t)).collect();
                MlT::Tuple(tys)
            }
            Param(p) => MlT::TVar(p.name.to_string()),
            Ref(_, ty, borkind) => {
                use rustc_ast::Mutability::*;
                match borkind {
                    Mut => MlT::MutableBorrow(box self.translate_ty(ty)),
                    Not => self.translate_ty(ty),
                }
            }
            _ => unimplemented!(),
        }
    }
}