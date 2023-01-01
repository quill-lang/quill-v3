pub mod elaborator;

#[salsa::jar(db = Db)]
pub struct Jar();

pub trait Db: fkernel::Db + qparse::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fkernel::Db + qparse::Db + salsa::DbWithJar<Jar> {}
