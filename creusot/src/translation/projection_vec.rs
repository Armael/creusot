use rustc_middle::mir::ProjectionElem;

pub type ProjectionVec<V, T> = Vec<ProjectionElem<V, T>>;

pub fn visit_projections<V, T>(v: &ProjectionVec<V, T>, mut f: impl FnMut(&V)) {
    v.iter().for_each(|elem| match elem {
        ProjectionElem::Index(v) => f(v),
        _ => {}
    })
}

pub fn visit_projections_mut<V, T>(v: &mut ProjectionVec<V, T>, mut f: impl FnMut(&mut V)) {
    v.iter_mut().for_each(|elem| match elem {
        ProjectionElem::Index(v) => f(v),
        _ => {}
    })
}
