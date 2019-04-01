import React from "react";
import { Rnd } from "react-rnd";
import { ScaleContext } from "../../contexts/scale";

const resizeStyles = pixels => {
  const corners = pixels * 4;
  const halved = pixels / 2;
  return {
    bottom: { height: pixels, bottom: -pixels },
    bottomLeft: { height: corners, width: corners, left: -pixels },
    bottomRight: {
      height: corners,
      width: corners,
      right: -pixels * 2,
      bottom: -pixels * 2
    },
    left: { width: pixels, right: -pixels },
    right: { width: pixels, marginLeft: "100%" },
    top: { height: pixels },
    topLeft: { height: corners, width: corners, left: -pixels, top: -pixels }
  };
};

const getMaxes = document => {
  const holder = document.querySelector(".w98");

  if (holder && (holder.offsetWidth < 640 || holder.offsetHeight < 480)) {
    return {
      maxWidth: Math.ceil(holder.offsetWidth - 5),
      maxHeight: Math.ceil(holder.offsetHeight - 32)
    };
  }

  return {};
};

class Window extends React.PureComponent {
  static contextType = ScaleContext;
  state = {
    x: this.props.initialX || 0,
    y: this.props.initialY || 0,
    height: this.props.initialHeight,
    width: this.props.initialWidth,
    maximized: false
  };

  updateLocation = (a, b) =>
    this.setState({ x: b.x, y: b.y, isDragging: false });
  resize = (e, direction, ref, delta, position) =>
    this.setState({
      width: ref.style.width,
      height: ref.style.height,
      ...position
    });
  maximize = () => this.setState({ maximized: true });
  restore = () => this.setState({ maximized: false });
  toggleDrag = val => () => this.setState({ isDragging: val });
  toggleResize = val => () => this.setState({ isResizing: val });

  render() {
    const resizeProps =
      this.props.resizable && !this.state.maximized
        ? {
            enableResizing: {
              bottom: true,
              bottomLeft: true,
              bottomRight: true,
              left: true,
              right: true,
              top: true,
              topLeft: true,
              topRight: false
            },
            resizeHandleStyles: resizeStyles(4),
            onResize: this.resize,
            onResizeStart: this.toggleResize(true),
            onResizeStop: this.toggleResize(false)
          }
        : { resizeHandleStyles: resizeStyles(0) };

    const maximizedProps = this.state.maximized
      ? {
          size: { width: "101%", height: "101%" },
          position: { x: -2, y: -3 },
          disableDragging: true
        }
      : undefined;
    return (
      <ScaleContext.Consumer>
        {context => (
          <>
            {this.state.isDragging && (
              <Rnd
                size={{ width: this.state.width, height: this.state.height }}
                position={{ x: this.state.x, y: this.state.y }}
                scale={context.scale}
              >
                {this.props.children({
                  ...this,
                  state: { ...this.state, isDragging: false }
                })}
              </Rnd>
            )}
            <Rnd
              size={{ width: this.state.width, height: this.state.height }}
              position={{ x: this.state.x, y: this.state.y }}
              dragHandleClassName="Window__title"
              onDragStart={this.toggleDrag(true)}
              onDragStop={!this.state.maximized && this.updateLocation}
              bounds=".w98"
              minWidth={this.props.minWidth}
              minHeight={this.props.minHeight}
              maxWidth={this.props.maxWidth}
              maxHeight={this.props.maxHeight}
              scale={context.scale}
              onMouseDown={
                this.props.moveToTop
                  ? () => this.props.moveToTop(this.props)
                  : undefined
              }
              {...resizeProps}
              {...maximizedProps}
              {...getMaxes(document)}
            >
              {this.props.children(this)}
            </Rnd>
          </>
        )}
      </ScaleContext.Consumer>
    );
  }
}

Window.defaultProps = {
  minWidth: 160,
  minHeight: 160,
  maxHeight: 448,
  maxWidth: 635,
  resizable: true,

  scale: 1,
  title: "Needs default"
};

export default Window;
