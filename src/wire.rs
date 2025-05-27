use rand::{seq::SliceRandom};
use crate::s::S;

#[derive(Clone, Debug)]
pub struct Wire {
    pub l0: S,
    pub l1: S,
    pub hash0: S,
    pub hash1: S,
    pub value: Option<bool>,
    pub label: Option<S>,
}

impl Wire {
    pub fn new() -> Self {
        let l0 = S::random();
        let l1 = l0.clone() + S::delta().sign_change(l0.lsb());
        let hash0 = l0.hash();
        let hash1 = l1.hash();
        Self {
            l0,
            l1,
            hash0,
            hash1,
            value: None,
            label: None,
        }
    }

    pub fn public_data(&self) -> Vec<S> {
        let mut hashs = vec![self.hash0.clone(), self.hash1.clone()];
        hashs.shuffle(&mut rand::rng());
        hashs
    }

    pub fn select(&self, selector: bool) -> S {
        if selector {
            self.l1.clone()
        }
        else {
            self.l0.clone()
        }
    }

    pub fn get_value(&self) -> bool {
        assert!(self.value.is_some());
        self.value.unwrap()
    }

    pub fn set_value(&mut self, bit: bool) {
        assert!(self.value.is_none());
        self.value = Some(bit);
        self.set_label(if bit {self.l1.clone()} else {self.l0.clone()});
    }

    pub fn set_label(&mut self, label: S) {
        self.label = Some(label);
    }

    pub fn get_label(&self) -> S {
        self.label.clone().unwrap()
    }
}
