package sla

const (
	ProofPhashMerkleZksnark = "PhashMerkleZksnark"
	ProofSsimMerkleZksnark  = "SsimZksnark"

	ProofPublicInputLeaf = "Leaf"
	ProofPublicInputRoot = "Root"
)

type SlaStorage struct {
	Url          string
	ProofType    string
	PublicInputs string
}

type ZkMerkleProof struct {
	Proof string `json:"proof"` // 192 byte
}

type ZkPublicInput struct {
	Leaf      string `json:"leaf"`
	Root      string `json:"root"`
	Auth_Path string `json:"auth_path"`
}

type ZkVerifyResult struct {
	Result string `json:"result"`
}
