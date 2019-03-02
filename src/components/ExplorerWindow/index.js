import React, { Component } from "react";
import { Rnd } from "react-rnd";
import { WindowExplorer } from "packard-belle";
import "./_styles.scss";

class Explorer extends Component {
  state = {
    width: this.props.initialWidth || this.props.minWidth,
    height: this.props.initialHeight || this.props.minHeight,
    x: 0,
    y: 0,
    maximized: false
  };

  updateLocation = (a, b) => this.setState({ x: b.x, y: b.y });
  resize = (e, direction, ref, delta, position) =>
    this.setState({
      width: ref.style.width,
      height: ref.style.height,
      ...position
    });
  maximize = () => this.setState({ maximized: true });
  restore = () => this.setState({ maximized: false });

  render() {
    return (
      <Rnd
        size={
          !this.state.maximized
            ? { width: this.state.width, height: this.state.height }
            : { width: "101%", height: "101%" }
        }
        position={
          !this.state.maximized
            ? { x: this.state.x, y: this.state.y }
            : { x: -2, y: -3 }
        }
        dragHandleClassName="Window__title"
        onDragStop={!this.state.maximized && this.updateLocation}
        disableDragging={this.state.maximized}
        enableResizing={this.state.maximized ? false : undefined}
        onResize={!this.state.maximized && this.resize}
        bounds=".w98"
        minWidth={this.props.minWidth}
        minHeight={this.props.minHeight}
        maxWidth={this.props.maxWidth}
        maxHeight={this.props.maxHeight}
        // scale={2}
      >
        <WindowExplorer
          title="Needs default"
          footer={[
            { text: "needs 100% width height" },
            { text: "overflow control" }
          ]}
          onClose={() => {
            /* needs default visibles */
          }}
          onMinimize={() => {}}
          onRestore={this.restore}
          onMaximize={this.maximize}
        >
          Children
        </WindowExplorer>
      </Rnd>
    );
  }
}

Explorer.defaultProps = {
  minWidth: 160,
  minHeight: 160,
  maxWidth: 635,
  maxHeight: 448,

  scale: 1,
  title: "Needs default"
};

export default Explorer;
