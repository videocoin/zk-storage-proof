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
	Proof string // 192 byte
}

type ZkPublicInput struct {
	Leaf string
	Root string
	Path string
}
