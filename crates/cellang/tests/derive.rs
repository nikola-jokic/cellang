#![cfg(feature = "derive")]

use cellang::types::NamedType;
use cellang::value::{IntoValue, TryFromValue};
use cellang::{CelStruct, Runtime};

#[derive(Clone, Debug, PartialEq, CelStruct)]
#[cel(type = "example.Address", doc = "Address record")]
struct Address {
    city: String,
}

#[derive(Clone, Debug, PartialEq, CelStruct)]
#[cel(type = "example.User", doc = "User record")]
struct User {
    #[cel(doc = "Display name")]
    name: String,
    address: Address,
    #[cel(rename = "is_active", doc = "Whether the user is active")]
    active: bool,
}

#[test]
fn cel_struct_generates_metadata_and_conversions() {
    let NamedType::Struct(user_meta) = User::cel_named_type() else {
        panic!("expected struct metadata");
    };
    assert_eq!(user_meta.name.as_str(), User::CEL_TYPE_NAME);
    assert_eq!(user_meta.doc.as_deref(), Some("User record"));

    let address_field = user_meta.fields.get("address").unwrap();
    assert_eq!(address_field.ty, Address::cel_type());

    let active_field = user_meta.fields.get("is_active").unwrap();
    assert_eq!(
        active_field.doc.as_deref(),
        Some("Whether the user is active"),
    );

    let user = User {
        name: "Ada".into(),
        address: Address {
            city: "London".into(),
        },
        active: true,
    };
    let value = user.clone().into_value();
    let roundtrip = User::try_from_value(&value).unwrap();
    assert_eq!(roundtrip, user);
}

#[test]
fn register_cel_type_reports_duplicates() {
    let mut builder = Runtime::builder();
    User::register_cel_type(&mut builder).unwrap();
    let err = User::register_cel_type(&mut builder).unwrap_err();
    assert!(
        err.to_string().contains(User::CEL_TYPE_NAME),
        "expected duplicate name in error, got {err}"
    );
}
