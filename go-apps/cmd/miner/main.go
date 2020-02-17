package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"os/exec"
	"os/user"

	"github.com/videocoin/zk-storage-proof/go-apps/sla"
)

func main() {
	usr, _ := user.Current()
	binFolder := flag.String("bin", "/usr/bin/", "folder zktrans containing binaries")
	workFolder := flag.String("work", usr.HomeDir+"/test/", "folder containing intermediate files")
	sla_id := flag.String("sla-id", "test slaid", "sla id")
	flag.Parse()

	// sla_id
	// TODO: Get Storage Sla and Get URL
	fmt.Println("Args ", *sla_id)

	// Create request
	slaStorage := sla.SlaStorage{
		Url:          "/tmp/testclips/test1.mp4",
		ProofType:    sla.ProofPhashMerkleZksnark,
		PublicInputs: "",
	}
	input := slaStorage.Url
	cmd := exec.Command(*binFolder+"extract-frame", "-f", "0", "-c", "300", "--scale", "--input", input, "--output", *workFolder+"scaled-frames.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err := cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("extracting frames")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	cmd = exec.Command(*binFolder+"rust-phash", *workFolder+"scaled-frames.txt", *workFolder+"phashes.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating phashes")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	// zksnarks proof
	cmd = exec.Command(*binFolder+"zkptrans", "zkporgenproof", *workFolder+"zkpor_crs.dat", *workFolder+"zkpor_proof.dat", *workFolder+"phashes.txt", *workFolder+"zkpor_witness.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating proof")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()
	// Read proof
	proof_file := *workFolder + "zkpor_proof.dat"
	proof_bytes, err := ioutil.ReadFile(proof_file)
	if err != nil {
		log.Fatal(err)
	}

	proof := sla.ZkMerkleProof{
		Proof: string(proof_bytes),
	}
	proof_json, err := json.Marshal(proof)

	cmd = exec.Command("vccli", "tx", "sla", "commitProof", *sla_id, string(proof_json), "--yes", "--from", "tester0")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating transaction")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	fmt.Println("Finished:", err)
}

func print(console io.ReadCloser) {
	scanner := bufio.NewScanner(console)
	scanner.Split(bufio.ScanWords)
	for scanner.Scan() {
		m := scanner.Text()
		fmt.Print(m + " ")
	}
}
