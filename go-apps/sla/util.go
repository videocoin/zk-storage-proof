package sla

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
)

type SlaOnly struct {
	Sla string `json:"sla"`
}

func GetSla(sla_id string) SlaStorage {
	//
	// Get the SLA corresponding to sla-id
	//
	var b1 bytes.Buffer
	var b2 bytes.Buffer
	cmd := exec.Command("vccli", "q", "sla", "get", sla_id)

	cmd.Stdout = &b1
	cmd.Stderr = &b2
	fmt.Println("generating transaction")
	err := cmd.Start()
	cmd.Wait()
	fmt.Println(b1.String())
	fmt.Println(b2.String())

	//
	// Get the SLA corresponding to sla-id
	//
	var slaOnly SlaOnly
	err = json.Unmarshal(b1.Bytes(), &slaOnly)
	if err != nil {
		fmt.Println("Error while getting sla: ", err)
		os.Exit(1)
	}

	var slaStorage SlaStorage
	err = json.Unmarshal([]byte(slaOnly.Sla), &slaStorage)
	if err != nil {
		fmt.Println("Error while getting slaStorage: ", err, slaStorage)
		os.Exit(1)
	}

	return slaStorage
}

func GetCommittedProof(sla_id string) ZkMerkleProof {
	//
	// Get the SLA corresponding to sla-id
	//
	var b1 bytes.Buffer
	var b2 bytes.Buffer
	cmd := exec.Command("vccli", "q", "sla", "commit", sla_id)

	cmd.Stdout = &b1
	cmd.Stderr = &b2
	fmt.Println("query for commit...")
	err := cmd.Start()
	cmd.Wait()
	fmt.Println(b1.String())
	fmt.Println(b2.String())

	//
	// Get the SLA corresponding to sla-id
	//
	var proof ZkMerkleProof
	err = json.Unmarshal(b1.Bytes(), &proof)
	if err != nil {
		fmt.Println("Error while getting commit: ", err)
		os.Exit(1)
	}

	return proof
}
