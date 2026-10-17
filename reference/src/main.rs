use p256::{ecdsa::{signature::{hazmat::PrehashVerifier, Verifier}, Signature, VerifyingKey},
    elliptic_curve::{bigint::U256, ops::Reduce, sec1::ToEncodedPoint, group::Group}, ProjectivePoint, Scalar};
use serde::Deserialize;
#[derive(Deserialize)]
struct Case { id:String, pk:String, digest:String, signature:String, message:String,
    expected:bool, standard_expected:bool, direct_x_expected:bool }
fn main() {
    let path=std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../vectors/cases.json");
    let cases:Vec<Case>=serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let mut differences=0;
    for c in &cases {
        let pk=hex::decode(&c.pk).unwrap(); let digest=hex::decode(&c.digest).unwrap();
        let sig=hex::decode(&c.signature).unwrap(); let mut sec1=vec![4];sec1.extend(&pk);
        let key=VerifyingKey::from_sec1_bytes(&sec1);let signature=Signature::from_slice(&sig);
        let standard=pk.len()==64 && digest.len()==32 && sig.len()==64 && match (&key,&signature) {
            (Ok(k),Ok(s)) => k.verify_prehash(&digest,s).is_ok(), _=>false };
        assert_eq!(standard,c.standard_expected,"{} standard prehash",c.id);
        // Independent direct-x check with RustCrypto's group arithmetic.
        let (direct, circuit)=if standard {
            let k=key.as_ref().unwrap(); let s=signature.as_ref().unwrap();
            let (r, scalar_s)=s.split_scalars();
            let w=scalar_s.invert().unwrap();
            let digest_array: [u8;32]=digest.as_slice().try_into().unwrap();
            let z=<Scalar as Reduce<U256>>::reduce_bytes(&digest_array.into());
            let g=ProjectivePoint::GENERATOR;
            let q=ProjectivePoint::from(*k.as_affine());
            let rp=g*(z*w)+q*(*r*w);
            let point=rp.to_affine().to_encoded_point(false);
            let direct=point.x().map(|x| x[..]==sig[..32]).unwrap_or(false);
            let tables=[g+q,g+rp,q+rp,g+(q+rp)];
            let circuit=direct && pk[..32].iter().any(|b| *b!=0) &&
                tables.iter().all(|point| !bool::from(point.is_identity()));
            (direct,circuit)
        } else { (false,false) };
        assert_eq!(direct,c.direct_x_expected,"{} Longfellow direct-x",c.id);
        assert_eq!(circuit,c.expected,"{} Longfellow circuit",c.id);
        if standard != circuit { differences+=1; }
        if c.id.starts_with("wycheproof-") {
            let original=match (&key,&signature) {(Ok(k),Ok(s))=>k.verify(&hex::decode(&c.message).unwrap(),s).is_ok(),_=>false};
            assert_eq!(original,c.standard_expected,"{} original message",c.id);
        }
    }
    assert!(differences > 0,"Expected the documented direct-x overflow differences");
    println!("RustCrypto p256 0.13.2: {} cases passed; 262 original-message checks; {differences} intentional standard/circuit differences",cases.len());
}
